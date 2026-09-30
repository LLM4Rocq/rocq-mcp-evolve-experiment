/-
LeanMcpEvolve.Gate — the correctness GATE: a fresh, anti-gaming recompile of
a candidate proof in its OWN process, independent of the in-session
completion check (`Driver.completionCheck`), which runs inside the same
process as the agent's tactics and can therefore be subverted by a tactic
block that executes arbitrary metaprograms (`run_tac`, `Lean.addDecl`,
`Lean.Kernel.Environment.addDeclWithoutChecking`). This is the Lean analogue
of rocq-mcp-evolve's `harness/gate.py`.

Six checks, in order, stopping at the first rejection (see `runInternal`):
1. reference/statement tamper (textual, `Text.findDecls`-based)
2. forbidden tokens in the target's proof, decided on Lean's own parsed
   `Syntax` tree (not a hand-rolled text scanner, so comment/string desync
   tricks cannot hide or fake a token)
3. a fresh compile of the whole candidate (`Lean.Elab.IO.processInput` with
   `cmdState? := none`)
4. the target is present, is not an `example`, and (when `--reference` is
   given) its type matches the reference's
5. `Lean.collectAxioms` of the target ⊆ {propext, Classical.choice, Quot.sound}
6. kernel replay: every constant the candidate itself added is re-added
   through the KERNEL (never `addDeclWithoutChecking`) into a fresh
   environment built from the candidate's header imports only

Step 6 uses Lean core's own `Lean.Environment.replay` (`Lean/Replay.lean`,
© 2023 Kim Morrison, Apache 2.0) rather than a hand-rolled topological sort:
it already threads dependencies in the right order, calls the KERNEL
(`Environment.addDeclCore`, `doCheck := true`) for every constant, and
reconstructs inductive/constructor/recursor declarations from their
`ConstantInfo`s -- exactly the "inductive replay ... when feasible" the task
anticipated as an open problem, except Lean already ships it. The only thing
`replay` doesn't give us is *which* constant the kernel rejected (it discards
that once it throws), so `LeanMcpEvolve.Gate.Replay` below is that same
algorithm adapted (with attribution, the same move `Driver.lean` already
makes for REPL internals) to tag the thrown error with the failing name, so
`run`/`runInternal` can report `kernel_replay_failed:<name>:<msg>`.
-/
import Lean
import REPL.Frontend
import LeanMcpEvolve.Text

namespace LeanMcpEvolve.Gate

open Lean
open LeanMcpEvolve

/-! ### verdict -/

structure Verdict where
  accepted   : Bool
  reason     : String := ""
  axioms     : List Name := []
  unreplayed : List Name := []
  deriving Inhabited

/-! ### small shared helpers -/

private def containsStr (s needle : String) : Bool := (s.splitOn needle).length > 1

private def isSorryWarningMsg (m : String) : Bool :=
  containsStr m "declaration uses" && containsStr m "sorry"

/-- Build a (possibly dotted) `Name` from a fully-qualified string -- copy of
`Driver.nameOfDotted` (Driver.lean is owned by another concurrent agent, so
this is duplicated rather than imported). -/
private def nameOfDotted (s : String) : Name :=
  ((s.splitOn ".").filter (· ≠ "")).foldl Name.mkStr Name.anonymous

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Remove the first occurrence of `x` from `l`, or `none` if absent. -/
private def removeFirst (l : List String) (x : String) : Option (List String) :=
  match l with
  | [] => none
  | h :: t => if h == x then some t else (removeFirst t x).map (h :: ·)

/-- Blank out a literal `import Mathlib.Tactic` header line (with spaces of
the same byte length, so every position after it is unaffected) -- used
*only* to obtain a source text that is safe to feed to `Text.findDecls` /
`targetProofSyntax`'s own internal parse (which needs the import to actually
*resolve*, else the resulting token table can be missing even core notations
and mis-locate everything after the header -- observed directly on a project
without Mathlib, exactly the situation this one tolerated import line exists
for, see `Gate`'s D9). The real compile (step 3) and the kernel-replay base
environment (step 6, `freshEnvFromHeader`) always use the untouched source,
so a project that genuinely has Mathlib available still elaborates/replays
against it for real; only position-finding treats the line as inert.

Known limitation: if the target's own proof text relies on genuinely new
*syntax* Mathlib.Tactic introduces (not just tactics/lemmas resolved during
elaboration), the blanked-header parse can still fail to locate it; when
that happens `targetProofSyntax` returns `none` and the forbidden-token
check passes conservatively, relying on the fresh-compile/kernel-replay
steps for safety instead (see the module doc). -/
private def blankMathlibImportLine (src : String) : String :=
  let hEnd := Text.headerEnd src
  let head := String.Pos.Raw.extract src ⟨0⟩ hEnd
  let rest := String.Pos.Raw.extract src hEnd src.rawEndPos
  let blankedHead := String.intercalate "\n" ((head.splitOn "\n").map fun l =>
    if l.trim == "import Mathlib.Tactic" then String.mk (List.replicate l.length ' ') else l)
  blankedHead ++ rest

/-! ### project root / search path (self-contained: mirrors
`Verify.axiomAudit`'s "single-shot `initSearchPath sp`" pattern per the task
briefing, and `Driver.projectRootFor`'s lakefile-ancestor walk -- duplicated
rather than imported since `Driver.lean` is owned by a concurrent agent). -/

private def hasLakefile (dir : System.FilePath) : IO Bool := do
  return (← (dir / "lakefile.lean").pathExists) || (← (dir / "lakefile.toml").pathExists)

private def findProjectRoot (file : System.FilePath) : IO System.FilePath := do
  let start := file.parent.getD (System.FilePath.mk ".")
  let rec go (d : System.FilePath) (fuel : Nat) : IO (Option System.FilePath) := do
    match fuel with
    | 0 => return none
    | fuel + 1 =>
      if ← hasLakefile d then
        return some d
      else
        match d.parent with
        | some p => if p == d then return none else go p fuel
        | none => return none
  match ← go start 200 with
  | some p => return p
  | none => return start

/-- `Lean.initSearchPath (← Lean.findSysroot) extraSp`, `extraSp` from
`lake env printenv LEAN_PATH` run in `root` -- exactly `Verify.axiomAudit`'s
approach (see the task briefing: "as `Verify.axiomAudit` does"). Safe to call
more than once per process (only ever adds search entries). -/
private def setupSearchPath (root : System.FilePath) : IO Unit := do
  let extraSp : System.SearchPath ←
    try
      let out ← IO.Process.output { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"], cwd := some root }
      if out.exitCode == 0 then
        pure (System.SearchPath.parse out.stdout.trimAscii.copy)
      else
        pure []
    catch _ => pure []
  Lean.initSearchPath (← Lean.findSysroot) extraSp

/-! ### 1. reference / statement tamper -/

/-- Text before the target's own `:=` (see `Text.Decl.stmtEndPos`'s doc
comment): the whole header plus every declaration preceding the target,
verbatim, plus the target's own statement text up to (not including) its
`:=`. -/
private def beforeText (src : String) (d : Text.Decl) : String :=
  String.Pos.Raw.extract src ⟨0⟩ d.stmtEndPos

/-- Text after the target's `endPos`: the rest of the file, verbatim. Same as
`Text.tailText`, spelled out here so the module doc's "before/after" naming
(see F3 in the report) reads directly against the code. -/
private def afterText (src : String) (d : Text.Decl) : String :=
  String.Pos.Raw.extract src d.endPos src.rawEndPos

/-- `candBefore`, with at most one line that is exactly `import Mathlib.Tactic`
removed from *the header portion only* (never from a declaration preceding
the target) -- the single tolerated addition, matching the session's preload
(see `Driver.buildPrefixText`). `none` if the candidate's header has no such
line to remove. -/
private def dropOneMathlibImportLine (candSrc : String) (candTarget : Text.Decl) : Option String :=
  let hEnd := Text.headerEnd candSrc
  let header := String.Pos.Raw.extract candSrc ⟨0⟩ hEnd
  let rest := String.Pos.Raw.extract candSrc hEnd candTarget.stmtEndPos
  (removeFirst (header.splitOn "\n") "import Mathlib.Tactic").map fun hLines =>
    String.intercalate "\n" hLines ++ rest

/-- `some reason` (`"statement_modified"` / `"prefix_modified"` /
`"suffix_modified"`) if `candSrc` tampers with anything but the target's own
proof, relative to `refSrc` -- see the module doc's step 1 and F3 in the
report.

F3 (report): the previous version compared only declaration texts (from
`Text.findDecls`) and header lines, so a candidate could smuggle in a
top-level command that is *not* itself a declaration -- `set_option ... true`,
`variable (h : ..)`, `open .. in`, `macro_rules`, `notation`, a bare
`#eval <arbitrary IO>` -- between declarations without tripping anything,
since such commands never show up in `Text.findDecls`'s declaration array at
all. This version instead compares raw bytes outside the proof region: the
statement text first (`"statement_modified"` when it differs -- checked
first since a differing statement subsumes everything below), then
everything from the start of the file up to the target's own `:=`
(`"prefix_modified"`, tolerating exactly one extra `import Mathlib.Tactic`
header line the candidate has and the reference doesn't -- see D9), then
everything after the target's `endPos` (`"suffix_modified"`). No declaration
array is needed any more: a smuggled command anywhere outside the target
shows up as a byte difference in one of these three regions regardless of
what kind of command it is. See D12 in `Tests/Gate.lean`. -/
def checkTamper (refSrc candSrc : String) (refTarget candTarget : Text.Decl) : Option String :=
  if Text.statementText refSrc refTarget ≠ Text.statementText candSrc candTarget then
    some "statement_modified"
  else
    let refBefore := beforeText refSrc refTarget
    let candBefore := beforeText candSrc candTarget
    let beforeOk :=
      candBefore == refBefore || dropOneMathlibImportLine candSrc candTarget == some refBefore
    if !beforeOk then
      some "prefix_modified"
    else if afterText candSrc candTarget ≠ afterText refSrc refTarget then
      some "suffix_modified"
    else
      none

/-! ### 2. forbidden tokens, decided on the parsed `Syntax` tree -/

private partial def findFirstOfKinds (kinds : Array Name) (stx : Syntax) : Option Syntax :=
  if kinds.contains stx.getKind then
    some stx
  else
    stx.getArgs.findSome? (findFirstOfKinds kinds)

private def declValKinds : Array Name :=
  #[``Lean.Parser.Command.declValSimple, ``Lean.Parser.Command.declValEqns,
    ``Lean.Parser.Command.whereStructInst]

/-- Parse `src`'s header + a `parseCommand` loop (no elaboration -- same
recipe as `Text.findDecls`), returning every top-level command's raw
`Syntax` (namespace/section/end commands included, unlike `Text.findDecls`,
since we only need positions to re-locate the target, not declaration
metadata). -/
private def parseAllCommands (src : String) : IO (Array Syntax) := do
  let inputCtx := Lean.Parser.mkInputContext src "<candidate>"
  let (header, parserState0, _headerMsgs) ← Lean.Parser.parseHeader inputCtx
  let (env, _procMsgs) ← Lean.Elab.processHeader header {} {} inputCtx
  let pmctx : Lean.Parser.ParserModuleContext := { env, options := {} }
  let mut mps := parserState0
  let mut messages : Lean.MessageLog := {}
  let mut cmds : Array Syntax := #[]
  let mut more := true
  while more do
    let (stx, mps', messages') := Lean.Parser.parseCommand inputCtx pmctx mps messages
    mps := mps'
    messages := messages'
    if Lean.Parser.isTerminalCommand stx then
      more := false
    else
      cmds := cmds.push stx
  return cmds

/-- The header-imports-only `Environment` (no commands processed) -- the
"fresh environment built from the candidate's header imports only" step 6
needs as the base for kernel replay. -/
private def freshEnvFromHeader (src : String) : IO Environment := do
  let inputCtx := Lean.Parser.mkInputContext src "<candidate>"
  let (header, _, _) ← Lean.Parser.parseHeader inputCtx
  let (env, _) ← Lean.Elab.processHeader header {} {} inputCtx
  return env

/-- The target declaration's proof `Syntax` (the term/tactic block after
`:=`; for `declValEqns`/`whereStructInst` styles, the whole node), located by
re-parsing `src` and matching the command whose `Syntax.getPos?` equals
`target.startPos` -- the very same position `Text.findDecls` recorded (same
input, same parse), so no duplication of its namespace-tracking is needed. -/
def targetProofSyntax (src : String) (target : Text.Decl) : IO (Option Syntax) := do
  let cmds ← parseAllCommands src
  match cmds.find? (fun stx => (stx.getPos?.getD ⟨1000000000⟩).byteIdx == target.startPos.byteIdx) with
  | none => return none
  | some stx =>
    let mut inner := stx
    while inner.getKind == ``Lean.Parser.Command.«in» && inner.getNumArgs ≥ 3 do
      inner := inner.getArg 2
    match findFirstOfKinds declValKinds inner with
    | none => return none
    | some dv =>
      if dv.getKind == ``Lean.Parser.Command.declValSimple && dv.getNumArgs > 1 then
        return some (dv.getArg 1)
      else
        return some dv

/-- Exact atom text (keywords/leading tokens) that make a proof suspect. -/
private def forbiddenAtoms : List String :=
  ["sorry", "native_decide", "unsafe", "run_tac", "run_cmd", "#eval", "#exit",
   "set_option", "axiom", "+native"]

/-- Exact identifier text (or last dotted component, to catch qualified
access such as `Lean.addDecl`) that make a proof suspect. -/
private def forbiddenIdents : List String :=
  ["admit", "addDecl", "addDeclWithoutChecking", "implemented_by", "extern",
   "ofReduceBool", "ofReduceNat", "sorryAx", "Lean.Elab", "Lean.Environment", "Lean.Kernel"]

/-- Identifiers whose *full* dotted text starts with one of these are
metaprogramming from a proof, regardless of the trailing component. -/
private def forbiddenIdentPrefixes : List String :=
  ["Lean.Elab.", "Lean.Meta.", "Lean.Environment."]

private def lastDotComponent (s : String) : String :=
  (s.splitOn ".").getLastD s

/-- Every forbidden token occurring in `stx`'s subtree, walking the raw
parsed `Syntax` (so a `sorry`/`#eval` hidden behind a comment/string desync
trick -- e.g. a trailing line comment followed by a bare block-comment
opener, or a string literal containing one -- cannot hide: comments never
make it into `Syntax` in the first place, and a genuine parse failure caused
by such a trick is instead caught by the fresh-compile step). -/
partial def forbiddenHits (stx : Syntax) : List String :=
  match stx with
  | .node _ _ args => args.toList.flatMap forbiddenHits
  | .atom _ val => if forbiddenAtoms.contains val then [val] else []
  | .ident _ _ n _ =>
    let s := n.toString
    let last := lastDotComponent s
    if forbiddenIdents.contains s then [s]
    else if forbiddenIdents.contains last then [last]
    else if forbiddenIdentPrefixes.any (fun p => s.startsWith p) then [s]
    else []
  | _ => []

/-- `some tok` for the first forbidden token found in the target's proof
region of `candSrc`, `none` if clean (including the "couldn't even locate
the target's proof syntax" case, e.g. a parse error inside it -- the
fresh-compile step catches that instead, see the module doc). -/
def forbiddenTokenCheck (candSrc : String) (target : Text.Decl) : IO (Option String) := do
  match ← targetProofSyntax candSrc target with
  | none => return none
  | some stx => return (forbiddenHits stx).head?

/-! ### 6. kernel replay -- `Lean.Environment.replay`, adapted to report the
name of the constant the kernel rejected (see the module doc's attribution
note). Copied from `Lean/Replay.lean`, © 2023 Kim Morrison, Apache 2.0,
https://github.com/leanprover/lean4, with `addDecl` changed to thread the
name being processed into the thrown error (`Lean.Environment.replay` itself
discards it): the thrown message is `"<name>\x00<msg>"` (a leading `Name`,
then a NUL byte -- never a plain space, since the kernel's own message
routinely contains spaces itself and a space-based split would silently
mis-parse those -- then the kernel's own message), so
`runInternal`/`splitReplayError` can split it back into `(name, msg)` on the
first NUL byte. -/
namespace Replay

structure Ctx where
  newConstants : Std.HashMap Name ConstantInfo

structure St where
  env : Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}

abbrev RM := ReaderT Ctx <| StateRefT St IO

def isTodo (name : Name) : RM Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

def throwNamed (name : Name) (msg : String) : RM Unit :=
  throw <| .userError s!"{name}\x00{msg}"

def throwKernelException (name : Name) (ex : Kernel.Exception) : RM Unit := do
  throwNamed name (← ex.toMessageData {} |>.toString)

/-- Add a declaration through the KERNEL (`Environment.addDeclCore`,
`doCheck := true` by default -- never `addDeclWithoutChecking`), tagging any
rejection with `name`. -/
def addDecl (name : Name) (d : Declaration) : RM Unit := do
  match (← get).env.addDeclCore 0 d (cancelTk? := none) with
  | .ok env => modify fun s => { s with env := env }
  | .error ex => throwKernelException name ex

mutual
partial def replayConstant (name : Name) : RM Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    if (← get).pending.contains name then
      match ci with
      | .defnInfo   info => addDecl name (Declaration.defnDecl   info)
      | .thmInfo    info => addDecl name (Declaration.thmDecl    info)
      | .axiomInfo  info => addDecl name (Declaration.axiomDecl  info)
      | .opaqueInfo info => addDecl name (Declaration.opaqueDecl info)
      | .inductInfo info =>
        let lparams := info.levelParams
        let nparams := info.numParams
        let all ← info.all.mapM fun n => do pure <| ((← read).newConstants[n]!)
        for o in all do
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
            pure ((← read).newConstants[n]!))
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstantsAsSet
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name
            type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addDecl name (Declaration.inductDecl lparams nparams types false)
      | .ctorInfo info =>
        modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
      | .recInfo info =>
        modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
      | .quotInfo _ =>
        addDecl name (Declaration.quotDecl)
      modify fun s => { s with pending := s.pending.erase name }

partial def replayConstants (names : NameSet) : RM Unit := do
  for n in names do replayConstant n
end

def checkPostponedConstructors : RM Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throwNamed ctor s!"invalid constructor {ctor}"
    | _, _ => throwNamed ctor s!"no such constructor {ctor}"

def checkPostponedRecursors : RM Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throwNamed ctor s!"invalid recursor {ctor}"
    | _, _ => throwNamed ctor s!"no such recursor {ctor}"

end Replay

/-- Like `Lean.Environment.replay`, but a kernel rejection is thrown as
`"<name>\0<msg>"` so the caller can recover which constant the kernel
rejected. -/
def replayNamed (newConstants : Std.HashMap Name ConstantInfo) (env : Environment) : IO Environment := do
  let mut remaining : NameSet := {}
  for (n, ci) in newConstants.toList do
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := ({ env, remaining } : Replay.St)) do
    ReaderT.run (r := ({ newConstants } : Replay.Ctx)) do
      for n in remaining do
        Replay.replayConstant n
      Replay.checkPostponedConstructors
      Replay.checkPostponedRecursors
  return s.env

/-- Split a `replayNamed` failure message on its leading `"<name>\x00"` token
into `(name, msg)`; a message with no NUL byte at all (some exception other
than one of `Replay.throwNamed`'s) is reported with a `"?"` name. -/
private def splitReplayError (msg : String) : String × String :=
  match msg.splitOn "\x00" with
  | culprit :: rest@(_ :: _) => (culprit, String.intercalate "\x00" rest)
  | _ => ("?", msg)

/-! ### type comparison (step 4) -/

private def runMeta (env : Environment) (opts : Options := {}) (act : Meta.MetaM α) : IO α :=
  (act.run' {} {} : CoreM α).toIO' { fileName := "<gate>", options := opts, fileMap := Lean.FileMap.ofString "" } { env }

/-- Pretty-print `e` in `env` with `pp.all true` (fully explicit: implicit
arguments, universe levels, and metavariable/instance elaboration all shown)
-- see F1 in the report: a plain `pp.all false` pretty-print can render two
genuinely different types identically (elided implicits/universes), which
would make `typesMatch`'s fallback wrongly agree that two different
statements are the same. -/
private def ppTypeIn (env : Environment) (e : Expr) : IO String := do
  let opts := ({} : Options).setBool `pp.all true
  let fmt ← runMeta env opts (Meta.ppExpr e)
  return toString fmt

/-- `ConstantInfo.type` equality between `n` as found in `candEnv` and in
`refEnv` -- `Expr`'s `BEq` (`Expr.eqv`, alpha-equivalence) first, falling
back to comparing the two types pretty-printed with `pp.all true` (fully
explicit, see `ppTypeIn`) in their own environments only when `Expr` equality
fails (the universe-parameter-naming corner case the task calls out); if
still unequal, the types genuinely differ. `true` when `n` is missing from
either side (nothing to compare; the caller has already separately checked
presence -- and, per F1, now rejects `reference_unusable` before ever
reaching this function when the reference side is the one missing it). -/
private def typesMatch (candEnv refEnv : Environment) (n : Name) : IO Bool := do
  match candEnv.find? n, refEnv.find? n with
  | some ci, some ri =>
    if ci.type == ri.type then
      return true
    else
      let s1 ← ppTypeIn candEnv ci.type
      let s2 ← ppTypeIn refEnv ri.type
      return s1 == s2
  | _, _ => return true

/-! ### axiom collection (step 5), `Environment`-pure (copy of
`Driver.collectAxiomsPure`'s trick: `Lean.CollectAxioms.collect`'s worker is
pure, so no `CoreM` context is needed). -/

private def collectAxiomsPure (env : Environment) (cname : Name) : List Name :=
  let (_, st) := ((Lean.CollectAxioms.collect cname).run env).run {}
  st.axioms.toList

/-! ### the pipeline

Each step below is its own top-level `def` returning `IO (Option Verdict)`
(`none` = "passed, keep going"), composed by `guardStep`. This is deliberate
rather than a single flattened `do` block with `match ... | none =>`
fall-through arms: with six sequential short-circuits some of which
themselves contain `let mut`/`for`, that flattening confused the `do`
elaborator's monad inference (each arm must stay a properly nested `IO`
action for the whole pipeline to keep resolving as plain `IO`, never the
underlying `EIO IO.Error`). -/

/-- Truncate a (possibly multi-line) diagnostic to a sane length for a
`Verdict.reason` -- reuses `Text.truncate`. -/
private def truncateReason (s : String) : String := Text.truncate 500 s

private def rejected (r : String) : Verdict := { accepted := false, reason := r }

/-- `chk`, then `cont` iff `chk` passed (returned `none`). -/
private def guardStep (chk : IO (Option Verdict)) (cont : IO Verdict) : IO Verdict := do
  match ← chk with
  | some v => return v
  | none => cont

/-- Step 1: reference/statement tamper (only when `reference?` is given).

F1 (report): every way the reference can be unusable for comparison -- the
path doesn't exist, it can't be read, or it has no declaration by
`theoremName` at all -- is reported as `reference_unusable:<detail>`, never
as a silent pass and never conflated with `target_missing` (which is
reserved for the *candidate's own* target being absent). See D10 in
`Tests/Gate.lean`. -/
private def step1Check (theoremName : String) (reference? : Option System.FilePath)
    (candSrc : String) (candTarget : Text.Decl) :
    IO (Option Verdict) := do
  match reference? with
  | none => return none
  | some refPath =>
    if !(← refPath.pathExists) then
      return some (rejected s!"reference_unusable:not_found:{refPath}")
    let refSrc ←
      try IO.FS.readFile refPath
      catch e => return some (rejected s!"reference_unusable:read_failed:{truncateReason (toString e)}")
    let refDecls ← Text.findDecls refSrc
    match Text.findDecl refDecls theoremName with
    | none => return some (rejected s!"reference_unusable:target_missing:{theoremName}")
    | some refTarget =>
      match checkTamper refSrc candSrc refTarget candTarget with
      | some r => return some (rejected r)
      | none => return none

/-- Step 2: forbidden tokens in the target's proof syntax (skippable, for
`Tests.Gate`'s defense-in-depth checks -- see `runInternal`'s doc comment). -/
private def step2Check (skipTokenCheck : Bool) (candSrc : String) (candTarget : Text.Decl) :
    IO (Option Verdict) := do
  if skipTokenCheck then
    return none
  match ← forbiddenTokenCheck candSrc candTarget with
  | some tok => return some (rejected s!"forbidden_token:{tok}")
  | none => return none

/-- Step 4's type-comparison half (presence is checked by the caller): when a
reference is given, it must compile enough to produce the target constant,
and that constant's type must match the candidate's.

F1 (report): the previous version returned `none` (pass, i.e. skip the type
check entirely) both when the reference failed to compile (any exception
from `processInput`, e.g. a missing/unreadable import) and when the target
name was simply absent from the compiled reference environment -- silently
disabling step 4's whole point. Both now REJECT with
`reference_unusable:<detail>` instead. This does *not* require the rest of
the reference file to be error-free (a reference is allowed the same kind of
unrelated holes/broken lemmas a task file can have, see F2): Lean's own
per-command error recovery still adds the target constant to the resulting
environment even when some other, unrelated declaration earlier or later in
the same file failed to elaborate, so only a target that is *truly*
unreachable (a fatal parse/import failure, or a target that never got a
constant of its own) is treated as reference-unusable here. -/
private def step4TypeCheck (reference? : Option System.FilePath) (candEnv : Environment) (cname : Name) :
    IO (Option Verdict) := do
  match reference? with
  | none => return none
  | some refPath =>
    let refSrc ←
      try IO.FS.readFile refPath
      catch e => return some (rejected s!"reference_unusable:read_failed:{truncateReason (toString e)}")
    let refCompiled ←
      try
        let r ← Lean.Elab.IO.processInput refSrc none {} (some refPath.toString)
        pure (Except.ok r)
      catch e => pure (Except.error (toString e))
    match refCompiled with
    | .error e => return some (rejected s!"reference_unusable:compile_error:{truncateReason e}")
    | .ok (_, refState, _, _) =>
      match refState.env.find? cname with
      | none => return some (rejected s!"reference_unusable:target_missing:{cname}")
      | some _ =>
        if ← typesMatch candEnv refState.env cname then
          return none
        else
          return some (rejected "statement_type_mismatch")

/-- Steps 4 (presence/example/type) through 6 (axioms, kernel replay), run
once the fresh compile (step 3) has produced `cmdStateAfter`/`msgs` with no
error and no sorry warning. -/
private def finishAfterCompile (candSrc : String) (candTarget : Text.Decl)
    (reference? : Option System.FilePath) (candEnv : Environment) : IO Verdict := do
  if candTarget.kind == "example" then
    return rejected "target_is_example"
  let cname := nameOfDotted candTarget.fullName
  match candEnv.find? cname with
  | none => return rejected "target_missing"
  | some _ =>
    guardStep (step4TypeCheck reference? candEnv cname) do
      -- step 5
      let axs := collectAxiomsPure candEnv cname
      match axs.find? (fun a => !standardAxioms.contains a) with
      | some bad => return rejected s!"axiom:{bad}"
      | none =>
        -- step 6
        let localConsts := candEnv.constants.map₂.toList
        match localConsts.find? (fun (n, ci) => ci.isAxiom && !standardAxioms.contains n) with
        | some (n, _) => return rejected s!"axiom:{n}"
        | none =>
          let skipped := localConsts.filterMap fun (n, ci) => if ci.isUnsafe || ci.isPartial then some n else none
          let freshEnv ← freshEnvFromHeader candSrc
          let newConstMap : Std.HashMap Name ConstantInfo := Std.HashMap.ofList localConsts
          let replayed ←
            try
              let e ← replayNamed newConstMap freshEnv
              pure (Except.ok e)
            catch e => pure (Except.error (toString e))
          match replayed with
          | .error msg =>
            let (culprit, m) := splitReplayError msg
            return rejected s!"kernel_replay_failed:{culprit}:{truncateReason m}"
          | .ok _ =>
            return { accepted := true, reason := "", axioms := axs, unreplayed := skipped }

/-- Step 3: a fresh compile of the whole candidate text (`cmdState? := none`),
then steps 4-6 via `finishAfterCompile`. -/
private def step3AndBeyond (candidate : System.FilePath) (candSrc : String) (candTarget : Text.Decl)
    (reference? : Option System.FilePath) : IO Verdict := do
  let compiled ←
    try
      let r ← Lean.Elab.IO.processInput candSrc none {} (some candidate.toString)
      pure (Except.ok r)
    catch e => pure (Except.error (toString e))
  match compiled with
  | .error e => return rejected s!"compile_error:{truncateReason e}"
  | .ok (_, cmdStateAfter, msgs, _) =>
    -- F2 (report): only messages positioned inside the *target's own* line
    -- range count towards `compile_error`/`sorry_warning` -- a task file can
    -- legitimately carry other holes (other `sorry` theorems) or an earlier
    -- broken proof Lean still admits, and none of that is the candidate's
    -- doing to fix. This is sound because (a) with `--reference`, everything
    -- outside the target's proof region is byte-identical to the reference
    -- (see `checkTamper`/F3), so any such pre-existing hole was already
    -- there and isn't something the candidate introduced, and (b) any
    -- dependency of the target itself on a sorried/broken declaration still
    -- surfaces as `sorryAx` in `collectAxiomsPure` (step 5), and every local
    -- declaration the candidate added is kernel-replayed (step 6) -- so a
    -- target that only *looks* fine because it leans on a hole elsewhere is
    -- still caught, just by a different step. See D11 in `Tests/Gate.lean`.
    let inTargetRange (m : Message) : Bool :=
      m.pos.line ≥ candTarget.startLine + 1 && m.pos.line ≤ candTarget.endLine + 1
    let errs := msgs.filter (fun m => m.severity == .error && inTargetRange m)
    match errs.head? with
    | some m =>
      let mtxt ← m.toString
      return rejected s!"compile_error:{truncateReason mtxt}"
    | none =>
      let mut sorryWarn := false
      for m in msgs do
        if m.severity == .warning && inTargetRange m && !sorryWarn then
          if isSorryWarningMsg (← m.toString) then
            sorryWarn := true
      if sorryWarn then
        return rejected "sorry_warning"
      else
        finishAfterCompile candSrc candTarget reference? cmdStateAfter.env

/-- `run`/`runInternal`'s six-step pipeline (see the module doc).
`skipTokenCheck` is a test-only escape hatch (step 2 is otherwise always
run) so `Tests.Gate` can verify the defense-in-depth claim that steps 3-6
independently reject what step 2 would already have caught -- see D2/D5/D6/D7
in `Tests/Gate.lean`. -/
def runInternal (candidate : System.FilePath) (theoremName : String)
    (reference? : Option System.FilePath) (project? : Option System.FilePath)
    (skipTokenCheck : Bool := false) : IO Verdict := do
  if !(← candidate.pathExists) then
    return rejected s!"candidate_not_found:{candidate}"
  let root ← match project? with
    | some p => pure p
    | none => findProjectRoot candidate
  setupSearchPath root
  let candSrc ← IO.FS.readFile candidate
  -- parse with the one tolerated header addition blanked out (see
  -- `blankMathlibImportLine`'s doc comment) -- extraction/compile below
  -- still always use the untouched `candSrc`.
  let candSrcParse := blankMathlibImportLine candSrc
  let candDecls ← Text.findDecls candSrcParse
  match Text.findDecl candDecls theoremName with
  | none => return rejected "target_missing"
  | some candTarget =>
    guardStep (step1Check theoremName reference? candSrc candTarget) <|
      guardStep (step2Check skipTokenCheck candSrcParse candTarget) <|
        step3AndBeyond candidate candSrc candTarget reference?

/-- Public library API (docs/PLAN.md-style signature per the task briefing):
always runs with the forbidden-token check enabled. -/
def run (candidate : System.FilePath) (theoremName : String)
    (reference? : Option System.FilePath) (project? : Option System.FilePath) : IO Verdict :=
  runInternal candidate theoremName reference? project? false

end LeanMcpEvolve.Gate
