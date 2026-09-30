/-
LeanMcpEvolve.Driver — the session engine on REPL snapshots (docs/PLAN.md §3/§4,
phase 2b deliverable 2). `Session.committed` mirrors rocq-mcp-evolve's list of
frozen `Vernacstate.t` snapshots: each committed tactic freezes an immutable
`REPL.ProofSnapshot`, so rollback is O(1) list-drop and speculation is "run
from a copy, discard it" (see `speculate`).

Where this file copies REPL internals verbatim (`getProofStatus`,
`findSorryProofSnapshot`, the wall-clock timeout harness) the code is adapted,
with attribution, from `REPL/Main.lean` exactly as Probe.lean already
established for phase 1 (`REPL.Main` cannot be imported directly: its `main`
would collide with ours, see docs/PHASE1_NOTES.md) -- attribution:
https://github.com/leanprover-community/repl REPL/Main.lean,
Copyright (c) 2023 Scott Morrison, Apache 2.0.

Import-timing deliverable (README "Excluding Mathlib import time from attempt
budgets"): this file now DOES import `LeanMcpEvolve.Mcp` (a previous version
of this doc note said it deliberately did not, for `debugLog`'s sake -- that
guard is still duplicated below rather than routed through `Mcp.debug`, but
the header-environment cache needs `Mcp.emitLog`/`Mcp.addImportMs` to produce
the one-record-per-header-load JSONL instrumentation the harness recipe
depends on, and `Mcp` itself imports nothing from `LeanMcpEvolve`, so this is
not a cycle). -/
import REPL.Frontend
import REPL.Lean.InfoTree
import REPL.Snapshots
import Lean.Data.FuzzyMatching
import Lean.Util.CollectAxioms
import LeanMcpEvolve.Text
import LeanMcpEvolve.Mcp

namespace LeanMcpEvolve.Driver

open Lean Elab
open LeanMcpEvolve

/-! ### small string/name helpers shared by this file -/

private def containsStr (s needle : String) : Bool := (s.splitOn needle).length > 1

/-- `"declaration uses 'sorry'"`-style warning, matching `lean_text`'s
`is_sorry_warning`. -/
private def isSorryWarningMsg (m : String) : Bool :=
  containsStr m "declaration uses" && containsStr m "sorry"

/-- Drop the linter's "Note: This linter can be disabled ..." trailer and trim,
matching `driver._clean_msg`. -/
private def cleanMsg (msg : String) : String :=
  let marker := "Note: This linter can be disabled"
  if containsStr msg marker then
    (String.intercalate marker [(msg.splitOn marker).headD msg]).trim
  else
    msg.trim

/-! ### copied REPL bits (see the module doc's attribution) -/

private partial def collectFVarsAux : Expr → NameSet
  | .fvar fvarId => NameSet.empty.insert fvarId.name
  | .app fm arg => (collectFVarsAux fm).merge (collectFVarsAux arg)
  | .lam _ binderType body _ => (collectFVarsAux binderType).merge (collectFVarsAux body)
  | .forallE _ binderType body _ => (collectFVarsAux binderType).merge (collectFVarsAux body)
  | .letE _ type value body _ =>
      ((collectFVarsAux type).merge (collectFVarsAux value)).merge (collectFVarsAux body)
  | .mdata _ expr => collectFVarsAux expr
  | .proj _ _ struct => collectFVarsAux struct
  | _ => NameSet.empty

private def collectFVars (e : Expr) : Meta.MetaM (Array Expr) := do
  let names := collectFVarsAux e
  let mut fvars := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then
      continue
    if names.contains ldecl.fvarId.name then
      fvars := fvars.push (.fvar ldecl.fvarId)
  return fvars

private partial def abstractAllLambdaFVars (e : Expr) : Meta.MetaM Expr := do
  let mut e' := e
  while e'.hasFVar do
    let fvars ← collectFVars e'
    if fvars.isEmpty then
      break
    e' ← Meta.mkLambdaFVars fvars e'
  return e'

/-- Copy of `REPL.getProofStatus`, retyped from `REPL`'s `M m String` to plain
`IO String` (its body never touches REPL's own `State`, see Probe.lean). -/
def getProofStatus (proofState : REPL.ProofSnapshot) : IO String := do
  match proofState.tacticState.goals with
  | [] =>
    let (res, _) ← proofState.runMetaM do
      match proofState.rootGoals with
      | [goalId] =>
        goalId.withContext do
        match proofState.metaState.mctx.getExprAssignmentCore? goalId with
        | none => return "Error: Goal not assigned"
        | some pf => do
          let pf ← instantiateMVars pf
          let pft ← Meta.inferType pf >>= instantiateMVars
          let expectedType ← Meta.inferType (mkMVar goalId) >>= instantiateMVars
          unless (← Meta.isDefEq pft expectedType) do
            return s!"Error: proof has type {pft} but root goal has type {expectedType}"
          let pf ← abstractAllLambdaFVars pf
          let pft ← Meta.inferType pf >>= instantiateMVars
          if pf.hasExprMVar then
            return "Incomplete: contains metavariable(s)"
          let usedLevels := collectLevelParams {} pft
          let usedLevels := collectLevelParams usedLevels pf
          let decl := Declaration.defnDecl {
            name := Name.anonymous
            type := pft
            value := pf
            levelParams := usedLevels.params.toList
            hints := ReducibilityHints.opaque
            safety := DefinitionSafety.safe }
          try
            let _ ← addDecl decl
          catch ex =>
            return s!"Error: kernel type check failed: {← ex.toMessageData.toString}"
          if pf.hasSorry then
            return "Incomplete: contains sorry"
          return "Completed"
      | _ => return "Not verified: more than one initial goal"
    return res
  | _ => return "Incomplete: open goals remain"

/-- Find the first *tactic-mode* `sorry` in `trees` and turn it into a
`ProofSnapshot`, adapted from `REPL.sorries` / `REPL.Main.runCommand`. -/
def findSorryProofSnapshot (trees : List InfoTree) (env? : Option Environment) :
    IO (Option REPL.ProofSnapshot) := do
  let sorries := trees.flatMap Lean.Elab.InfoTree.sorries
  for (ctx, sorryType, _pos, _endPos) in sorries do
    match sorryType with
    | .tactic g =>
      let lctx ← ctx.runMetaM {} do
        match ctx.mctx.findDecl? g with
        | some decl => return decl.lctx
        | none => throwError "unknown metavariable '{g}'"
      let s ← REPL.ProofSnapshot.create ctx lctx env? [g] none
      return some s
    | .term _ none => pure ()
    | .term lctx (some ty) =>
      let s ← REPL.ProofSnapshot.create ctx lctx env? [] none [ty]
      return some s
  return none

/-- Trace to stderr iff `LEAN_MCP_DEBUG` is set to a non-empty value -- mirrors
`Mcp.debug`'s contract (stdout carries only JSON-RPC, so this file, which must
not import `Mcp`, writes its own copy of the same guard). -/
def debugLog (msg : String) : IO Unit := do
  match ← IO.getEnv "LEAN_MCP_DEBUG" with
  | some v => if v.isEmpty then pure () else IO.eprintln s!"[lean-mcp-evolve] {msg}"
  | none => pure ()

/-! ### timeouts -/

namespace Config

private def parseFloat (s : String) : Option Float :=
  match s.trim.splitOn "." with
  | [whole] => whole.toNat?.map Float.ofNat
  | [whole, frac] =>
    match whole.toNat?, frac.toNat? with
    | some w, some f =>
      let denom : Float := (10.0 : Float) ^ (Float.ofNat frac.length)
      some (Float.ofNat w + Float.ofNat f / denom)
    | _, _ => none
  | _ => none

def envFloat (name : String) (default : Float) : IO Float := do
  match ← IO.getEnv name with
  | some s => return (parseFloat s).getD default
  | none => return default

def envNat (name : String) (default : Nat) : IO Nat := do
  match ← IO.getEnv name with
  | some s => return s.trim.toNat?.getD default
  | none => return default

/-- `LEAN_STEP_TIMEOUT`, default 30s (docs/PLAN.md §4). -/
def stepTimeout : IO Float := envFloat "LEAN_STEP_TIMEOUT" 30.0
/-- `LEAN_TRY_TIMEOUT`, default 15s (prototype `session_server.try_timeout`). -/
def tryTimeout : IO Float := envFloat "LEAN_TRY_TIMEOUT" 15.0
/-- `LEAN_AUTO_TIMEOUT`, default 6s (docs/PLAN.md §4). -/
def autoTimeout : IO Float := envFloat "LEAN_AUTO_TIMEOUT" 6.0
/-- `LEAN_SEARCH_TIMEOUT`, default 25s (docs/PLAN.md §4). -/
def searchTimeout : IO Float := envFloat "LEAN_SEARCH_TIMEOUT" 25.0
/-- `LEAN_OPEN_TIMEOUT`, default 600s (prototype `session_server.open_timeout`). -/
def openTimeout : IO Float := envFloat "LEAN_OPEN_TIMEOUT" 600.0
/-- `LEAN_BUILD_TIMEOUT`, default 600s (docs/PLAN.md §4/§5). -/
def buildTimeout : IO Float := envFloat "LEAN_BUILD_TIMEOUT" 600.0
/-- `LEAN_MAX_HEARTBEATS`: kept at Lean's own default (200000), *not* raised,
per docs/PHASE1_NOTES.md ("do NOT raise it") -- the wall-clock mechanism is
what actually bounds a call; heartbeats remain Lean's own safety net. -/
def maxHeartbeats : IO Nat := envNat "LEAN_MAX_HEARTBEATS" 200000

end Config

/-! ### wall-clock timeout harness (docs/PHASE1_NOTES.md, ported from
Probe.lean's `runWithTimeout`, generalised to any `IO` action) -/

private def floatSecToMs (f : Float) : Nat :=
  if f ≤ 0 then 0 else (f * 1000).toUInt64.toNat

/-- Run `task` (already started via `IO.asTask`) with a wall-clock budget:
poll `IO.hasFinished` every 50ms instead of blocking on `task.get`, so a
runaway tactic (e.g. `decide` on a big `Fin` search) never blocks the server;
on timeout we simply stop waiting (`none`) and leave the task running in the
background, exactly as Probe.lean's `runWithTimeout` documents. -/
private def waitTask (task : Task (Except IO.Error α)) (budgetSecs : Float) :
    IO (Option (Except IO.Error α)) := do
  let budgetMs := floatSecToMs budgetSecs
  let start ← IO.monoMsNow
  let rec poll (fuel : Nat) : IO Bool := do
    if (← IO.hasFinished task) then
      return true
    else
      match fuel with
      | 0 => return false
      | fuel + 1 =>
        if (← IO.monoMsNow) - start ≥ budgetMs then
          return (← IO.hasFinished task)
        else
          IO.sleep 50
          poll fuel
  if ← poll (budgetMs / 50 + 2) then
    return some task.get
  else
    return none

/-- Run `tacticStr` against `snap` under a wall-clock + heartbeat budget,
installing a fresh `IO.CancelToken` as `runWithTimeout` does; `maxHeartbeats`
is `Config.maxHeartbeats` (Lean's own default, unraised -- see
docs/PHASE1_NOTES.md). -/
private inductive RunOutcome where
  | ok (snap : REPL.ProofSnapshot)
  | error (msg : String)
  | timeout

private def runUnitWithTimeout (snap : REPL.ProofSnapshot) (tacticStr : String)
    (budgetSecs : Float) : IO RunOutcome := do
  -- `Core.Context.maxHeartbeats` is the *internal* tick count, 1000x the
  -- user-facing `set_option maxHeartbeats`/`LEAN_MAX_HEARTBEATS` value (see
  -- `Lean.Util.Heartbeats`'s own doc comment and `Lean.CoreM.getMaxHeartbeats`).
  let maxHb ← Config.maxHeartbeats
  let tk ← IO.CancelToken.new
  let snap := { snap with
    coreContext := { snap.coreContext with cancelTk? := some tk, maxHeartbeats := maxHb * 1000 } }
  let task ← IO.asTask (snap.runString tacticStr)
  match ← waitTask task budgetSecs with
  | some (.ok snap') => return .ok snap'
  | some (.error e) => return .error (toString e)
  | none => tk.set; return .timeout

/-- Run an arbitrary `IO` action (whole-file / prefix elaboration) under a
wall-clock budget only (no cancel token -- these aren't `ProofSnapshot` runs). -/
private def runIOWithTimeout (act : IO α) (budgetSecs : Float) : IO (Option (Except IO.Error α)) := do
  waitTask (← IO.asTask act) budgetSecs

/-! ### outcomes and the session -/

inductive ErrKind where
  | unknownRef (name : String)
  | syntax
  | other
  deriving Repr, Inhabited

inductive Stop where
  | done | error | timeout
  deriving Repr, DecidableEq, Inhabited

structure Outcome where
  nOk        : Nat
  stop       : Stop
  errUnit?   : Option Nat := none
  errText    : String := ""
  errMsg     : String := ""
  errKind    : ErrKind := .other
  goals      : List String := []
  complete   : Bool := false
  msgs       : List String := []
  timeoutS   : Float := 0
  deriving Inhabited

structure Session where
  file        : System.FilePath
  root        : System.FilePath
  name        : String
  prefixState : Lean.Elab.Command.State
  prefixText  : String
  stmtText    : String
  tail        : String
  indent      : String
  /-- The file's *original* source text, exactly as read at `open` (before any
  `import Mathlib.Tactic` preload injection). Together with `target` this lets
  `candidateText` rebuild the candidate as a byte-for-byte copy of `orig`
  outside the target's value, instead of re-deriving that text from
  `stmtText`'s *normalised* (right-trimmed, `" := by"`-suffixed) form -- see
  `candidateText`'s doc comment for why the normalised form alone produced a
  candidate that byte-differed from the reference outside the proof
  (`suffix_modified`/`prefix_modified` false rejections). -/
  orig        : String
  /-- The target declaration as located in `orig` by `Text.findDecls`
  (`startPos`/`stmtEndPos`/`endPos` are what `candidateText` slices `orig`
  with). -/
  target      : Text.Decl
  base        : REPL.ProofSnapshot
  committed   : List (String × REPL.ProofSnapshot) := []
  complete    : Bool := false
  preloaded   : Option String := none
  earlierErrors : Nat := 0

private def curSnap (s : Session) : REPL.ProofSnapshot :=
  match s.committed with
  | (_, snap) :: _ => snap
  | [] => s.base

/-- The environment of the session's current snapshot (head of `committed`,
or `base` if nothing committed yet) -- phase 3 (`Session.lean`) needs this for
tactic-availability probing (`auto_close`'s portfolio filter) and for parsing
agent text with `Text.splitUnits`/`Text.scanForbidden`'s identifier scan
against the session's actual token table, mirroring the Python original's use
of `s.header`/the live server's environment for the same purposes. -/
def sessionEnv (s : Session) : Environment :=
  (curSnap s).coreState.env

/-! ### search path / project root -/

initialize initializedRoots : IO.Ref (List System.FilePath) ← IO.mkRef []

private def hasLakefile (dir : System.FilePath) : IO Bool := do
  return (← (dir / "lakefile.lean").pathExists) || (← (dir / "lakefile.toml").pathExists)

/-- `Lean.initSearchPath (← Lean.findSysroot)`; if `LEAN_PATH` is unset and
`root` has a lakefile ancestor, run `lake env printenv LEAN_PATH` in `root`
and add those directories -- the "project load-path auto-discovery" of
docs/PLAN.md §3. Idempotent per `root` (cached in `initializedRoots`). -/
def initSearchPath (root : System.FilePath) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  if (← initializedRoots.get).contains root then
    return ()
  initializedRoots.modify (root :: ·)
  if (← IO.getEnv "LEAN_PATH").isSome then
    return ()
  if !(← hasLakefile root) then
    return ()
  try
    let out ← IO.Process.output { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"], cwd := some root }
    if out.exitCode == 0 then
      let dirs := (out.stdout.trim.splitOn ":").filter (· ≠ "")
      for d in dirs do
        Lean.searchPathRef.modify (· ++ [System.FilePath.mk d])
  catch _ =>
    pure ()

/-- Nearest ancestor of `file` with `lakefile.lean`/`lakefile.toml`, else
`LEAN_PROJECT_ROOT`, else the file's own directory. -/
def projectRootFor (file : System.FilePath) : IO System.FilePath := do
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
  | none =>
    match ← IO.getEnv "LEAN_PROJECT_ROOT" with
    | some r => return System.FilePath.mk r
    | none => return start

/-! ### header-environment cache ("pay `import Mathlib` once per process")

README "Excluding Mathlib import time from attempt budgets": `import Mathlib`
costs 7-120s and used to be paid again by every `open`/`build`/probe that
processes a *different* file's prefix text, even when that file imports
exactly the same modules -- the old prefix cache below was keyed by
`(file, prefixText)`, so a second file with an identical import list still
reprocessed the header from scratch. This section factors header processing
(`import ...` lines only) out into its own cache, keyed by the sorted,
deduplicated import list alone, so it is shared across every file/target that
needs the same modules -- `computePrefixState`/`diagnoseCore` below use it
underneath the existing `(file, prefixText)` cache, and `openFile`'s injected
`import Mathlib.Tactic` preload naturally becomes a different, separately
cached, import list (`Text.importsOf src ++ ["Mathlib.Tactic"]`), never
confused with the file's own unpreloaded header. -/

/-- Canonicalise an import list for cache-key/synthetic-header purposes:
dedup, then sort -- two files importing the same modules in different order
(or with duplicates) must hit the same cache entry. -/
def normalizeImports (imports : List String) : List String :=
  (imports.eraseDups.toArray.qsort (· < ·)).toList

/-- A synthetic "header-only" Lean source: one `import` line per module, in
`normalizeImports`'s canonical order -- fed to `processInput` with
`cmdState? := none` to obtain the `Command.State` right after header
processing, with no other commands. -/
def syntheticHeaderText (imports : List String) : String :=
  String.intercalate "" (imports.map fun m => s!"import {m}\n")

/-- `Command.State` for "just the header", keyed by `normalizeImports`'s
canonical form of the import list. A single growing association list (not a
`HashMap`) is fine here: the number of *distinct* import lists any one
process ever sees in practice is tiny (usually one -- "Mathlib", or a
project's own single import set) even though the number of FILES/targets
opened against it can be large, which is exactly the cost this cache is
meant to amortize. -/
initialize headerCache :
    IO.Ref (List (List String × Lean.Elab.Command.State)) ← IO.mkRef []

/-- Compute (or fetch from `headerCache`) the `Command.State` for `imports`'
header alone. Emits exactly one `{"kind":"import", ...}` JSONL record via
`Mcp.emitLog` for THIS call (cache hit or miss, prewarm or not -- see the
README section this deliverable adds) and adds this call's own wall time
(0 on a hit) to `Mcp`'s process-wide `import_ms_total` counter. -/
def getHeaderState (imports : List String) (timeoutS : Float) (prewarm : Bool := false) :
    IO (Except String (Lean.Elab.Command.State × Bool × Float)) := do
  let key := normalizeImports imports
  let modulesJson := toJson key
  match (← headerCache.get).find? (fun (k, _) => k == key) with
  | some (_, st) =>
    let ts ← Mcp.wallClockNow
    Mcp.emitLog
      [ ("ts", toJson ts), ("kind", Json.str "import"), ("modules", modulesJson)
      , ("dur_ms", toJson (0.0 : Float)), ("cached", toJson true), ("prewarm", toJson prewarm) ]
    return .ok (st, true, 0.0)
  | none =>
    let t0 ← IO.monoMsNow
    let text := syntheticHeaderText key
    let res ← runIOWithTimeout (Lean.Elab.IO.processInput text none {} (some "<header>")) timeoutS
    let t1 ← IO.monoMsNow
    let durMs := (t1 - t0).toFloat
    Mcp.addImportMs durMs
    let ts ← Mcp.wallClockNow
    match res with
    | none =>
      Mcp.emitLog
        [ ("ts", toJson ts), ("kind", Json.str "import"), ("modules", modulesJson)
        , ("dur_ms", toJson durMs), ("cached", toJson false), ("prewarm", toJson prewarm)
        , ("error", Json.str s!"timeout (>{timeoutS}s)") ]
      return .error s!"timeout (>{timeoutS}s) loading imports {key}"
    | some (.error e) =>
      Mcp.emitLog
        [ ("ts", toJson ts), ("kind", Json.str "import"), ("modules", modulesJson)
        , ("dur_ms", toJson durMs), ("cached", toJson false), ("prewarm", toJson prewarm)
        , ("error", Json.str (toString e)) ]
      return .error (toString e)
    | some (.ok (headerState, _, _, _)) =>
      headerCache.modify (fun l => (key, headerState) :: l)
      Mcp.emitLog
        [ ("ts", toJson ts), ("kind", Json.str "import"), ("modules", modulesJson)
        , ("dur_ms", toJson durMs), ("cached", toJson false), ("prewarm", toJson prewarm) ]
      return .ok (headerState, false, durMs)

/-- The single in-flight/completed background header prewarm task, if one was
started (`startHeaderPrewarm`) -- keyed by the (canonical) import list it
covers, so `acquireHeaderState` can tell whether a given request should wait
on it. `none` until `startHeaderPrewarm` is called; never replaced afterwards
(a process only ever prewarms once, mirroring `Session.eagerOpenTaskRef`). -/
initialize headerPrewarmRef :
    IO.Ref (Option (List String × Task (Except IO.Error (Except String (Lean.Elab.Command.State × Bool × Float)))))
    ← IO.mkRef none

/-- Start loading `imports`' header in the background on a DEDICATED thread
(never a pool worker -- see `Session.startEagerOpen`'s doc comment for why:
a pool worker starved the nested elaboration task this same `waitTask`
machinery polls for). No-op if a prewarm was already started (never races two
concurrent prewarms) or if `imports` is empty *and* no explicit list was
asked for -- callers only invoke this when they actually have something to
warm. Tags the resulting `import` JSONL record `prewarm: true`. -/
def startHeaderPrewarm (imports : List String) (timeoutS : Float) : IO Unit := do
  match ← headerPrewarmRef.get with
  | some _ => return ()
  | none =>
    let key := normalizeImports imports
    let task ← IO.asTask (prio := .dedicated) (getHeaderState imports timeoutS (prewarm := true))
    headerPrewarmRef.set (some (key, task))

/-- Block until the background header-prewarm task (if any was started) has
finished, regardless of which import list it covers. `Session.startEagerOpen`
calls this BEFORE it does anything else, so the prewarm task's own
`processInput` call (on its own dedicated thread) never runs CONCURRENTLY
with the eager open's (on ITS OWN dedicated thread) -- two Lean-runtime
`processInput` calls racing from two different dedicated threads, each
spawning its own nested default-priority elaboration task, was observed to
occasionally deadlock the shared task pool (a `lean_finalize_task_manager`
hang at process exit, threads stuck in `processCommandsIncrementally`'s
internal task wait) under load; serializing prewarm strictly before eager
open removes that concurrent-`processInput` window entirely. A no-op, and
fast, once the prewarm task has completed (the common case by the time this
runs, since prewarm is started first in `Main.lean`). -/
def awaitHeaderPrewarm : IO Unit := do
  match ← headerPrewarmRef.get with
  | some (_, task) => discard (IO.wait task)
  | none => pure ()

/-- Acquire the header state for `imports`: if a background prewarm task
covers exactly this (canonicalised) import list, wait for it first (so the
real `import` work happens at most once, whichever of the prewarm task or
this caller reaches it first), then fetch from `headerCache` (a cache hit at
that point, unless the prewarm itself failed, in which case this falls
through to its own fresh attempt). Otherwise -- no matching prewarm -- go
straight to `getHeaderState`. This is what makes `open`/the lazy
`LEAN_TASK_FILE` open "wait for the prewarm task if it covers the needed
import list; otherwise import normally" (README). -/
def acquireHeaderState (imports : List String) (timeoutS : Float) :
    IO (Except String (Lean.Elab.Command.State × Bool × Float)) := do
  match ← headerPrewarmRef.get with
  | some (pkey, task) =>
    if pkey == normalizeImports imports then
      let _ ← IO.wait task
      getHeaderState imports timeoutS (prewarm := true)
    else
      getHeaderState imports timeoutS (prewarm := false)
  | none => getHeaderState imports timeoutS (prewarm := false)

/-- The header import list `openFile` will use for `file`: its own imports,
plus the injected `Mathlib.Tactic` preload line under exactly the same
conditions `openFile` itself decides to inject it (project has a `Mathlib`
package, the file doesn't already import `Mathlib`/`Mathlib.Tactic`,
`LEAN_PRELOAD` isn't `0`). Used only to pick WHICH import list to warm at
startup (`Main.lean`'s prewarm wiring) -- `openFile` computes its own
decision independently (and retries without preload on failure, which this
best-effort duplicate does not model), so a mismatch here only costs a
missed cache hit, never a correctness bug. `none` if `file` doesn't exist. -/
def resolveHeaderImports (file : System.FilePath) : IO (Option (List String)) := do
  if !(← file.pathExists) then
    return none
  let src ← IO.FS.readFile file
  let root ← projectRootFor file
  initSearchPath root
  let fileImports := Text.importsOf src
  let hasMathlibPkg ← (root / ".lake" / "packages" / "mathlib").pathExists
  let alreadyImportsMathlib := fileImports.contains "Mathlib" || fileImports.contains "Mathlib.Tactic"
  let preloadDisabled := (← IO.getEnv "LEAN_PRELOAD") == some "0"
  let wantPreload := hasMathlibPkg && !alreadyImportsMathlib && !preloadDisabled
  return some (fileImports ++ (if wantPreload then ["Mathlib.Tactic"] else []))

/-! ### prefix-state cache ("prefix replay memoization") -/

initialize prefixCache :
    IO.Ref (Option (System.FilePath × String × Lean.Elab.Command.State × Nat)) ← IO.mkRef none

/-- Process `prefixText`'s commands from a cached header environment
(`acquireHeaderState headerImports`, or `headerR?` when the caller already
fetched it -- e.g. `openFile`'s own diagnosis pass, when its import list is
identical, so this doesn't emit a second redundant `import` JSONL record for
the very same header) instead of reprocessing `import ...` lines every time --
`prefixText` always starts with a header block (`Text.headerEnd`), so only
the text AFTER it (the file's earlier declarations, if any) is fed to
`processInput` here. Returns the resulting `Command.State`, the error count,
and whether the header itself was a cache hit (surfaced to the agent as
`open`'s `import_cached` log field). -/
private def computePrefixState (file : System.FilePath) (prefixText : String) (headerImports : List String)
    (timeoutS : Float)
    (headerR? : Option (Except String (Lean.Elab.Command.State × Bool × Float)) := none) :
    IO (Except String (Lean.Elab.Command.State × Nat × Bool)) := do
  let headerR ← match headerR? with
    | some r => pure r
    | none => acquireHeaderState headerImports timeoutS
  match headerR with
  | .error e => return .error e
  | .ok (headerState, headerCached, _) =>
    let hEnd := Text.headerEnd prefixText
    let restText := String.Pos.Raw.extract prefixText hEnd prefixText.rawEndPos
    match ← runIOWithTimeout (Lean.Elab.IO.processInput restText (some headerState) {} (some file.toString)) timeoutS with
    | none => return .error s!"timeout (>{timeoutS}s)"
    | some (.error e) => return .error (toString e)
    | some (.ok (_, cmdStateAfter, msgs, _)) =>
      let errs := (msgs.filter (·.severity == .error)).length
      prefixCache.set (some (file, prefixText, cmdStateAfter, errs))
      return .ok (cmdStateAfter, errs, headerCached)

private def getPrefixState (file : System.FilePath) (prefixText : String) (headerImports : List String)
    (timeoutS : Float)
    (headerR? : Option (Except String (Lean.Elab.Command.State × Bool × Float)) := none) :
    IO (Except String (Lean.Elab.Command.State × Nat × Bool)) := do
  match ← prefixCache.get with
  | some (cf, ct, cstate, cErrs) =>
    if cf == file && ct == prefixText then
      return .ok (cstate, cErrs, true)
    else
      computePrefixState file prefixText headerImports timeoutS headerR?
  | none => computePrefixState file prefixText headerImports timeoutS headerR?

/-! ### whole-file diagnosis (shared by `openFile`'s default-target selection
and the public `diagnoseFile`) -/

structure Hole where
  name : String
  what : String
  deriving Repr, Inhabited

/-- `headerR?`, when given, is an ALREADY-fetched `acquireHeaderState` result
for `src`'s own (unpreloaded) import list -- `openFile` fetches this once
(for its default-target diagnosis) and passes it in here so this function
does not call `acquireHeaderState` a second time for the very same import
list (which would otherwise emit a redundant `import` JSONL record every
single `open` call, one from diagnosis and one from prefix processing, even
though both usually want the exact same header). `none` (the default) is
`diagnoseFile`'s own standalone use, which has no such pre-fetch to reuse. -/
private def diagnoseCore (file : System.FilePath) (src : String) (decls : Array Text.Decl)
    (timeoutS : Float)
    (headerR? : Option (Except String (Lean.Elab.Command.State × Bool × Float)) := none) :
    IO (Array (Text.Decl × Option Hole) × Nat × List String) := do
  -- Header (imports only) is processed via the shared cache; only the text
  -- AFTER it goes through a fresh `processInput` call, so message positions
  -- below come back relative to THAT slice, not the original `src` -- see
  -- `headerLineCount`'s use just below for the correction back to `src`'s own
  -- (0-based) line numbering, which `decls`' `startLine`/`endLine` (from
  -- `Text.findDecls src`, unaffected by this split) are already in.
  let headerR ← match headerR? with
    | some r => pure r
    | none => acquireHeaderState (Text.importsOf src) timeoutS
  match headerR with
  | .error e =>
    return (decls.map fun d => (d, some { name := d.fullName, what := e }), 0, [])
  | .ok (headerState, _, _) =>
    let hEnd := Text.headerEnd src
    let headerLineCount := ((String.Pos.Raw.extract src ⟨0⟩ hEnd).toList.filter (· == '\n')).length
    let restSrc := String.Pos.Raw.extract src hEnd src.rawEndPos
    match ← runIOWithTimeout (Lean.Elab.IO.processInput restSrc (some headerState) {} (some file.toString)) timeoutS with
    | none =>
      return (decls.map fun d =>
        (d, some { name := d.fullName, what := s!"timeout (>{timeoutS}s) elaborating the file" }), 0, [])
    | some (.error e) =>
      return (decls.map fun d => (d, some { name := d.fullName, what := toString e }), 0, [])
    | some (.ok (_, _cmdStateAfter, msgs, _)) =>
      let lines := (src.splitOn "\n").toArray
      let mut out : Array (Text.Decl × Option Hole) := #[]
      let mut okCount := 0
      for d in decls do
        let mut hole? : Option Hole := none
        for m in msgs do
          if hole?.isNone then
            let origLine1 := m.pos.line + headerLineCount
            let ln := origLine1 - 1
            if ln ≥ d.startLine && ln ≤ d.endLine then
              if m.severity == .error then
                let lineText := lines.getD ln ""
                let msgStr ← m.toString
                hole? := some {
                  name := d.fullName
                  what := s!"fails at `{lineText.trim}` (line {origLine1}): {Text.truncate 240 msgStr}" }
              else if m.severity == .warning then
                let msgStr ← m.toString
                if isSorryWarningMsg msgStr then
                  hole? := some {
                    name := d.fullName
                    what := "uses `sorry`: the file compiles but this statement is not proved" }
        out := out.push (d, hole?)
        if hole?.isNone then
          okCount := okCount + 1
      let mut outside : List String := []
      for m in msgs do
        let origLine1 := m.pos.line + headerLineCount
        let ln := origLine1 - 1
        if m.severity == .error && !decls.any (fun d => ln ≥ d.startLine && ln ≤ d.endLine) then
          let msgStr ← m.toString
          outside := outside ++ [s!"line {origLine1}: {Text.truncate 240 msgStr}"]
      return (out, okCount, outside)

/-- Whole-file diagnosis: elaborate `file` (with its own imports, no session
touched) and, for each declaration, report a `Hole` if it fails to elaborate
or uses `sorry`, else count it OK. Third component: error messages outside
any declaration's range. Pure w.r.t. any open session. -/
def diagnoseFile (file : System.FilePath) (timeoutS : Float) :
    IO (Except String (List Hole × Nat × List String)) := do
  if !(← file.pathExists) then
    return .error s!"no such file: {file}"
  let src ← IO.FS.readFile file
  let root ← projectRootFor file
  initSearchPath root
  let decls ← Text.findDecls src
  let (diag, okCount, outside) ← diagnoseCore file src decls timeoutS
  return .ok (diag.toList.filterMap (fun (_, h) => h), okCount, outside)

/-! ### open -/

private def buildPrefixText (src : String) (startPos : String.Pos.Raw) (withPreload : Bool) : String :=
  if withPreload then
    let hEnd := Text.headerEnd src
    let head := String.Pos.Raw.extract src ⟨0⟩ hEnd
    let rest := String.Pos.Raw.extract src hEnd startPos
    head ++ "import Mathlib.Tactic\n" ++ rest
  else
    String.Pos.Raw.extract src ⟨0⟩ startPos

/-- `open{file, theorem?}` (docs/PLAN.md §4). `Except.error` carries a message
for the agent; `Except.ok` is `(session, note, headerCached)` where `note` is
`""` or a `"\n(...)"`/`"\nNOTE: ..."` suffix, and `headerCached` is whether
the target's header-environment (import list) was already in `headerCache`
when this call needed it (surfaced as `open`'s `import_cached` log field, see
README "Excluding Mathlib import time from attempt budgets").

`prewarm`, when `true`, is `Session.startEagerOpen`'s own signal that THIS
call is itself the background prewarm mechanism for a `LEAN_TASK_FILE`
preset (started before `initialize` is answered, on a dedicated thread) --
its header load is fetched directly via `getHeaderState (prewarm := true)`
(tagging its `import` JSONL record accordingly) rather than through
`acquireHeaderState`'s separate-background-task-matching machinery, which
is reserved for the `LEAN_PREWARM_IMPORTS`-triggered task (see
`Main.startPrewarm`'s doc comment for why `LEAN_TASK_FILE` no longer starts
its OWN separate header-prewarm task: doing so doubled the per-session
dedicated-OS-thread count and was implicated in an intermittent
`lean_finalize_task_manager` exit hang under suite A's load, 2026-09-07).
Runtime `open` calls (explicit tool calls, the lazy `LEAN_TASK_FILE` open)
leave this `false`, going through `acquireHeaderState` as before so they
still wait on/benefit from an explicit `LEAN_PREWARM_IMPORTS` task if one is
in flight and covers the same imports. -/
def openFile (file : System.FilePath) (theorem? : Option String) (timeoutS : Float)
    (prewarm : Bool := false) : IO (Except String (Session × String × Bool)) := do
  if !(← file.pathExists) then
    return .error s!"no such file: {file}"
  let src ← IO.FS.readFile file
  let root ← projectRootFor file
  initSearchPath root
  let decls ← Text.findDecls src
  if decls.isEmpty then
    return .error s!"no declarations found in {file}"
  -- Fetch the file's own (unpreloaded) header ONCE here -- used for
  -- diagnosis below, and reused (not re-fetched) by the prefix processing
  -- further down whenever it turns out to want the exact same import list
  -- (i.e. no `Mathlib.Tactic` preload), so a single `open` call emits one
  -- `import` JSONL record for its header, not two.
  let fileImports := Text.importsOf src
  let headerR0 ← (if prewarm then getHeaderState fileImports timeoutS (prewarm := true)
    else acquireHeaderState fileImports timeoutS : IO (Except String (Lean.Elab.Command.State × Bool × Float)))
  let (diag, okCount, _outside) ← diagnoseCore file src decls timeoutS (some headerR0)
  let targetR : Except String (Text.Decl × String) :=
    match theorem? with
    | some name =>
      match Text.findDecl decls name with
      | some d => .ok (d, "")
      | none =>
        let names := String.intercalate ", " (decls.toList.map (·.fullName))
        .error s!"no declaration named '{name}' in {file} (declarations: {names}); pass theorem:<name>"
    | none =>
      match diag.toList.find? (fun (_, h) => h.isSome) with
      | some (d, _) =>
        let holeNames := diag.toList.filterMap (fun (dd, h) => if h.isSome then some dd.fullName else none)
        let n := holeNames.length
        let plural := if n == 1 then "" else "s"
        let joined := String.intercalate ", " holeNames
        .ok (d, s!"\n({n} hole{plural} in the file; proving the first: {joined})")
      | none =>
        .error s!"{file} has no error and no sorry ({okCount} declaration(s) OK) — nothing to prove; pass theorem:<name>"
  match targetR with
  | .error e => return .error e
  | .ok (d, holeNote) =>
  if d.style == .pattern || d.style == .«none» then
    return .error
      s!"declaration '{d.fullName}' is pattern-matching decl (or has no single proof position); \
        pass theorem:<name> for a provable declaration"
  let hasMathlibPkg ← (root / ".lake" / "packages" / "mathlib").pathExists
  let alreadyImportsMathlib := fileImports.contains "Mathlib" || fileImports.contains "Mathlib.Tactic"
  let preloadDisabled := (← IO.getEnv "LEAN_PRELOAD") == some "0"
  let wantPreload := hasMathlibPkg && !alreadyImportsMathlib && !preloadDisabled
  let mut preloaded? : Option String := if wantPreload then some "import Mathlib.Tactic" else none
  let mut headerImports := fileImports ++ (if wantPreload then ["Mathlib.Tactic"] else [])
  let mut prefixText := buildPrefixText src d.startPos wantPreload
  -- `headerR0` (fetched once above) is only reusable here when this call's
  -- header import list is exactly `fileImports` -- i.e. no preload -- since
  -- that is the ONLY case where it's the same header `diagnoseCore` already
  -- fetched; the preloaded header (`fileImports ++ ["Mathlib.Tactic"]`) is a
  -- genuinely different import list and gets its own fresh acquire/record.
  let mut prefixR ←
    (if wantPreload then
      (do
        let headerR1 ← (if prewarm then getHeaderState headerImports timeoutS (prewarm := true)
          else acquireHeaderState headerImports timeoutS : IO (Except String (Lean.Elab.Command.State × Bool × Float)))
        getPrefixState file prefixText headerImports timeoutS (some headerR1))
    else
      getPrefixState file prefixText headerImports timeoutS (some headerR0))
  if wantPreload then
    if let .error _ := prefixR then
      preloaded? := none
      headerImports := fileImports
      prefixText := buildPrefixText src d.startPos false
      prefixR ← getPrefixState file prefixText headerImports timeoutS (some headerR0)
  match prefixR with
  | .error e => return .error s!"failed to process the file prefix: {e}"
  | .ok (prefixState, earlierErrors, headerCached) =>
    let stmtText := Text.statementText src d
    let tail := Text.tailText src d
    let indent := String.mk (List.replicate (d.col + 2) ' ')
    let stmtInput := stmtText ++ " sorry\n"
    match ← runIOWithTimeout (Lean.Elab.IO.processInput stmtInput (some prefixState) {} (some file.toString)) timeoutS with
    | none => return .error s!"timeout (>{timeoutS}s) elaborating the statement"
    | some (.error e) => return .error s!"statement fails to elaborate: {e}"
    | some (.ok (cmdStateBeforeEcho, _cmdStateAfterStmt, stmtMsgs, stmtTrees)) =>
      match ← findSorryProofSnapshot stmtTrees cmdStateBeforeEcho.env with
      | none =>
        let mut errs : List String := []
        for m in stmtMsgs do
          if m.severity == .error then
            errs := errs ++ [← m.toString]
        return .error s!"statement fails to elaborate: {String.intercalate "\n" errs}"
      | some base =>
        let s : Session := {
          file, root, name := d.fullName, prefixState, prefixText, stmtText, tail, indent
          orig := src, target := d
          base, committed := [], complete := false, preloaded := preloaded?, earlierErrors }
        let earlierNote :=
          if earlierErrors > 0 then
            s!"\nNOTE: {earlierErrors} error(s) in earlier declarations of the file (Lean admits \
              them so this statement is reachable; `build` lists them)."
          else ""
        return .ok (s, holeNote ++ earlierNote, headerCached)

/-! ### evaluate / speculate / rollback / goals -/

private def classifyMsg (msg : String) : ErrKind := Id.run do
  for marker in ["nknown identifier", "nknown constant", "nknown namespace"] do
    if containsStr msg marker then
      let after := String.intercalate marker ((msg.splitOn marker).drop 1)
      let arr := after.toList.toArray
      let n := arr.size
      let mut i := 0
      while i < n && !(arr[i]! == '`' || arr[i]! == '\'' || arr[i]! == '‘') do
        i := i + 1
      if i < n then
        let mut j := i + 1
        while j < n && !(arr[j]! == '`' || arr[j]! == '\'' || arr[j]! == '’' || arr[j]!.isWhitespace) do
          j := j + 1
        return .unknownRef (String.mk ((arr.toList.drop (i + 1)).take (j - i - 1)))
  let head := (msg.splitOn "\n").headD msg
  if ["unknown tactic", "unexpected token", "expected ", "unexpected end of input", "unterminated"].any
      (containsStr head) then
    return .syntax
  return .other

private def queryTactics : List String :=
  ["exact?", "apply?", "rw?", "simp?", "simp_all?", "aesop?", "norm_num?", "hint"]

private def isIdentStartCh (c : Char) : Bool := c.isAlpha || c == '_'
private def isIdentContCh (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'

/-- Every identifier-shaped word in `s`, left to right (a minimal local
tokenizer -- `Text.lean`'s equivalent helpers are private to that file). -/
private def wordsOf (s : String) : List String := Id.run do
  let chars := s.toList.toArray
  let n := chars.size
  let mut i := 0
  let mut out : List String := []
  while i < n do
    if isIdentStartCh chars[i]! then
      let mut buf := chars[i]!.toString
      i := i + 1
      while i < n && isIdentContCh chars[i]! do
        buf := buf.push chars[i]!
        i := i + 1
      out := out ++ [buf]
    else
      i := i + 1
  return out

/-- First query-tactic-shaped word in `unit` (a `queryTactics` entry, or any
word ending in `?`) -- generalises the "unit IS a query tactic" check to "unit
CONTAINS one", so a search tactic nested inside a `·` bullet or `<;>`
combinator (e.g. `· exact?`) is still found; the Python original locates the
same token precisely via its LSP diagnostic's column range (see the module
doc's note on why that isn't available here), so this is an approximation:
the *first* such word in the unit's text, textual, not position-verified. -/
private def findQueryToken (unit : String) : Option String :=
  (wordsOf unit).find? (fun w => queryTactics.contains w || w.endsWith "?")

/-- Replace the first whole-word occurrence of `tok` in `s` with `repl`,
`none` if `tok` does not occur as its own word. -/
private def spliceToken (s tok repl : String) : Option String := Id.run do
  let chars := s.toList.toArray
  let n := chars.size
  let tokChars := tok.toList.toArray
  let m := tokChars.size
  let mut i := 0
  while i < n do
    if isIdentStartCh chars[i]! then
      let start := i
      let mut j := i + 1
      while j < n && isIdentContCh chars[j]! do
        j := j + 1
      if j - start == m && chars.extract start j == tokChars then
        let head := String.mk (chars.toList.take start)
        let tail := String.mk (chars.toList.drop j)
        return some (head ++ repl ++ tail)
      i := j
    else
      i := i + 1
  return none

private def formatNewMsgs (old cur : REPL.ProofSnapshot) : IO (List String) := do
  let raw := cur.newMessages old
  let mut out : List String := []
  for m in raw do
    if m.severity == .information || m.severity == .warning then
      let str ← m.toString
      if !containsStr str "Try this" && !isSorryWarningMsg str && !containsStr str "tactic does nothing" then
        let c := cleanMsg str
        if c ≠ "" then
          out := out ++ [c]
  return out

def proofScript (s : Session) : String :=
  Text.indentBlock (s.committed.reverse.map Prod.fst).toArray s.indent

def finishedDeclaration (s : Session) : String :=
  s.stmtText ++ "\n" ++ proofScript s

/-- The candidate written to disk for the gate (`Session.writeCandidate`).

Must be byte-identical to `s.orig` everywhere outside the target's own value,
with exactly one tolerated addition (the injected `import Mathlib.Tactic`
line already folded into `s.prefixText` when `s.preloaded` is set) -- that is
what `Gate.checkTamper`'s `beforeText`/`afterText` comparisons (raw byte
slices of the *candidate*, re-parsed with `Text.findDecls`, against the same
slices of the *reference*) require to accept a genuine proof.

Two bugs this used to have, both from building the statement/tail portions
out of `s.stmtText`/`s.tail` as if they already were exactly the candidate's
final bytes:

1. `s.stmtText` is `Text.statementText`'s *normalised* form: the raw
   `startPos..stmtEndPos` slice right-trimmed and `" := by"`-suffixed. That
   normalisation is exactly what makes the *statement* comparison
   (`Text.statementText` applied to both sides) tolerant of incidental
   whitespace before `:=`, but it is wrong to also use it as the literal
   bytes written to the candidate: if the original had anything but a single
   space before `:=`, the candidate's raw `beforeText` (compared byte-for-byte,
   not normalised) would then differ from the reference's, misfiring
   `prefix_modified`. Fixed by slicing `s.orig` from `target.startPos` to
   `target.stmtEndPos` *verbatim* (preserving whatever precedes `:=`) and
   appending the literal `":= by\n"` only once, right before the proof.
2. An extra hardcoded `"\n"` was inserted between the proof and `s.tail`.
   `s.tail` (`Text.tailText`) already *starts* with whatever newline(s)
   originally followed the old value (e.g. the `sorry` that used to be
   there) -- that newline is not consumed by `stmtEndPos`/`endPos`, it lives
   in the tail. Adding another `"\n"` in front of it inserted a byte that
   is not in `s.orig`, so re-parsing the candidate located the target's new
   `endPos` right after the proof and read one extra `"\n"` (or, for a
   same-line/no-trailing-newline value, a spurious new `"\n"`) into
   `afterText`, which the reference's `afterText` does not have --
   `suffix_modified` on an otherwise-correct proof. Fixed by not adding a
   `"\n"` before `s.tail` at all. -/
def candidateText (s : Session) : String :=
  s.prefixText
  ++ String.Pos.Raw.extract s.orig s.target.startPos s.target.stmtEndPos
  ++ ":= by\n" ++ proofScript s ++ s.tail

/-! ### completion audit -- goals closed, re-elaboration clean, no `sorry`,
axioms allowlisted (README "Verification" §1)

Build a (possibly dotted) `Name` from a fully-qualified string -- same trick
`Gate.lean`'s own copy (`nameOfDotted`) uses; kept independent here rather
than shared via import, exactly as `Gate.lean`'s own doc comment on its copy
explains (`Gate.lean` depends on `Text.lean`, not on `Driver.lean`, so
sharing this one helper is not worth introducing that dependency edge). -/
private def nameOfDotted (s : String) : Name :=
  ((s.splitOn ".").filter (· ≠ "")).foldl Name.mkStr Name.anonymous

/-- The three axioms a genuine proof is allowed to rest on -- same allowlist
`Gate.lean`'s `standardAxioms` uses for its own, independent audit. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- `Environment`-pure axiom collection (`Lean.CollectAxioms.collect`'s
worker needs no `CoreM` context, only the `Environment`) -- same trick
`Gate.lean`'s `collectAxiomsPure` uses. -/
private def collectAxiomsPure (env : Environment) (cname : Name) : List Name :=
  let (_, st) := ((Lean.CollectAxioms.collect cname).run env).run {}
  st.axioms.toList

/-- The name an `example` target's re-elaboration is spliced under for the
axiom audit below. `example` elaborates under a transient internal name
(`_example`, see `Lean/Elab/DefView.lean`'s `mkDefViewOfExample`) that is
NOT added to the environment permanently -- confirmed empirically: a bare
`#print axioms _example` run immediately after an `example` command fails
with "unknown constant `_example`" -- so there is no name `completionCheck`
could look the finished constant up by afterward. `example` targets need a
REAL name to run `Lean.collectAxioms` against. -/
private def exampleCheckName : String := "_lean_mcp_evolve_example_check"

/-- Splice the target's own leading `example` keyword token into
`theorem <exampleCheckName>`, leaving binders/type/`:= by` untouched, so
re-elaborating the result produces the identical proof term under a name
`completionCheck` CAN look up afterward. The keyword is located on the
comment-stripped text (so a stray "example" inside a preceding doc comment
can't be matched instead of the real keyword) as the first word-boundary
occurrence of the literal token `"example"`; returns `stmtText` UNCHANGED if
none is found, which makes `completionCheck` fail closed via its own
"constant not found after re-elaboration" branch below rather than silently
skip the audit. -/
private def spliceExampleKeyword (stmtText : String) : String := Id.run do
  let clean := Text.stripComments stmtText
  let chars := stmtText.toList.toArray
  let cleanChars := clean.toList.toArray
  let n := chars.size
  let isCont (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''
  let tok := "example".toList.toArray
  let m := tok.size
  let mut i := 0
  let mut found : Option Nat := none
  while i + m ≤ n && found.isNone do
    if cleanChars.extract i (i + m) == tok then
      let beforeOk := i == 0 || !isCont cleanChars[i-1]!
      let afterOk := i + m == n || !isCont cleanChars[i+m]!
      if beforeOk && afterOk then
        found := some i
    i := i + 1
  match found with
  | none => stmtText
  | some idx =>
    let before := String.mk (chars.extract 0 idx).toList
    let after := String.mk (chars.extract (idx + m) n).toList
    before ++ "theorem " ++ exampleCheckName ++ after

/-- In-session completion audit, restored 2026-09-08 to what the README
"Verification" section describes (the 2026-09-06 "refusal parity" change had
shallowed this down to "goals empty + re-elaboration has no error", on the
premise that rocq-mcp-evolve's own session server accepts `Admitted.`
in-session exactly as it accepts a real `Qed.` -- that premise was found
FALSE: the Rocq server's session completion means "the proof term is closed
and the declaration elaborates" only because Rocq's `Qed.` itself is the
only vernacular command it accepts as completing a proof, and `Qed.` FAILS
outright after an `admit` -- `Admitted.` is a distinct command the tactic-
running tools never send, so there was never an in-session "sorry/admit
completes" case in the Rocq server to match parity with. Concretely, ALL
FOUR of the following must hold:
1. Goals empty (`tacticState.goals`).
2. Re-elaborating the finished declaration (statement + committed script) as
   a command in the prefix state, with `debug.skipKernelTC` forced OFF (so
   the kernel actually re-checks the produced term, not just the
   elaborator's own bookkeeping), produces NO error messages.
3. That re-elaboration ALSO produces no `declaration uses 'sorry'` warning
   (`isSorryWarningMsg`) -- a `sorry` unit is refused up front by
   `Session.rejectSorryUnit` before it can ever be committed, but this is a
   second, independent backstop (e.g. a tactic that manufactures a `sorry`
   term without the literal token, such as a `Try this:`-suggested tactic
   splicing one in) that fails closed even if the up-front refusal is ever
   bypassed.
4. `Lean.collectAxioms` of the re-elaborated target constant is a SUBSET of
   `standardAxioms` (`propext`, `Classical.choice`, `Quot.sound`) -- an
   injected custom axiom, `native_decide`'s `Lean.ofReduceBool`, etc. all
   fail this. `example` targets have no nameable constant to look this up
   for (see `spliceExampleKeyword`'s doc comment), so they are re-elaborated
   under a synthetic name instead; if that constant still can't be found
   (e.g. the splice itself failed to locate the `example` keyword), this
   fails CLOSED rather than best-effort-passing on the missing lookup.

`getProofStatus` (REPL's own kernel-add + `hasSorry` check) is NOT called
from here -- it stays defined above for the gate/tests, and its coarser
"Incomplete: contains sorry" verdict would be redundant with checks 3-4
above, not a replacement for them (it has no axiom-allowlist notion at
all). -/
def completionCheck (s : Session) : IO Bool := do
  let cur := curSnap s
  if !cur.tacticState.goals.isEmpty then
    return false
  let isExample := s.target.kind == "example"
  let stmtForCheck := if isExample then spliceExampleKeyword s.stmtText else s.stmtText
  let checkNameStr := if isExample then exampleCheckName else s.name
  let fullDecl := stmtForCheck ++ "\n" ++ proofScript s ++ "\n"
  -- force the kernel to re-check this re-elaboration regardless of whatever
  -- ambient `debug.skipKernelTC` the *session* itself was opened with.
  let opts := Lean.Options.empty.setBool `debug.skipKernelTC false
  let budget ← Config.openTimeout
  match ← runIOWithTimeout (Lean.Elab.IO.processInput fullDecl (some s.prefixState) opts (some s.file.toString)) budget with
  | none => debugLog s!"completionCheck: timeout (>{budget}s) re-elaborating {s.name}"; return false
  | some (.error e) => debugLog s!"completionCheck: {s.name}: {e}"; return false
  | some (.ok (_, cmdStateAfter, msgs, _)) =>
    if msgs.any (·.severity == .error) then
      return false
    let mut sorryWarn := false
    for m in msgs do
      if !sorryWarn && m.severity == .warning then
        if isSorryWarningMsg (← m.toString) then
          sorryWarn := true
    if sorryWarn then
      debugLog s!"completionCheck: {s.name}: sorry warning in re-elaboration"
      return false
    let cname := nameOfDotted checkNameStr
    match cmdStateAfter.env.find? cname with
    | none =>
      debugLog s!"completionCheck: {s.name}: constant {cname} not found after re-elaboration"
      return false
    | some _ =>
      let axs := collectAxiomsPure cmdStateAfter.env cname
      match axs.find? (fun a => !standardAxioms.contains a) with
      | some bad =>
        debugLog s!"completionCheck: {s.name}: disallowed axiom {bad}"
        return false
      | none => return true

/-- Run `units` in order from the session's current snapshot, committing each
success; the first failure/timeout stops the call (docs/PLAN.md's `step`).
Search tactics (`exact?`, ...) whose result contains a `Try this:` message are
re-run as the suggested tactic and *that* is what gets committed -- see the
module doc for why this replaces LSP-diagnostic column splicing with a
straight re-run from the same snapshot (we have no diagnostic columns here,
only `ProofSnapshot.newMessages`, which is text only). -/
def evaluate (s : Session) (units : Array String) (timeoutS : Float) : IO (Outcome × Session) := do
  let mut cur := curSnap s
  let mut acc : Array (String × REPL.ProofSnapshot) := #[]
  let mut msgs : List String := []
  let mut stop := Stop.done
  let mut errUnit? : Option Nat := none
  let mut errText := ""
  let mut errMsg := ""
  let mut errKind := ErrKind.other
  let mut i := 0
  let n := units.size
  while i < n && stop == Stop.done do
    let unit := units[i]!
    if unit.trim.startsWith "#" then
      stop := Stop.error
      errUnit? := some i
      errText := unit
      errMsg := "query units (`#...`) must be run via runQuery, not evaluate"
    else
      match ← runUnitWithTimeout cur unit timeoutS with
      | .timeout =>
        stop := Stop.timeout
        errUnit? := some i
        errText := unit
        errMsg := s!"timeout (>{timeoutS}s)"
      | .error msg =>
        stop := Stop.error
        errUnit? := some i
        errText := unit
        errMsg := msg
        errKind := classifyMsg msg
      | .ok snap0 =>
        -- `ProofSnapshot.runString`'s `Except` only reflects a hard parse/
        -- elaboration exception (e.g. a genuinely unparseable tactic); a
        -- term-elaboration failure INSIDE an otherwise well-formed tactic
        -- (e.g. `exact <unknown identifier>`) is Lean's normal error-recovery
        -- path: it logs an `.error`-severity message and synthesizes a
        -- placeholder so elaboration can continue, meaning `tacticState.goals`
        -- can come back *empty* for a unit that did not actually prove
        -- anything. The Python/LSP original never has this gap (every
        -- diagnostic, recovered or not, is visible via `d.is_error`), so this
        -- checks the new message log the same way `_analyse` does: any new
        -- `.error` message for this unit is a failure, not a success.
        let rawNew0 := snap0.newMessages cur
        match ← (rawNew0.filter (·.severity == .error)).foldlM
            (fun acc? m => match acc? with | some _ => pure acc? | none => do pure (some (cleanMsg (← m.toString))))
            (none : Option String) with
        | some em =>
          stop := Stop.error
          errUnit? := some i
          errText := unit
          errMsg := em
          errKind := classifyMsg em
        | none =>
          let newMsgs0 ← formatNewMsgs cur snap0
          -- `formatNewMsgs` deliberately *excludes* "Try this" messages from
          -- `newMsgs0` (they are not meant to be shown as plain progress
          -- messages, see its doc comment), so the "Try this" search below
          -- must run over the raw, unfiltered message log instead.
          let mut tryThisMsg? : Option String := none
          for m in rawNew0 do
            if tryThisMsg?.isNone then
              let str ← m.toString
              if containsStr str "Try this" then
                tryThisMsg? := some str
          -- Search tactics (`exact?`, ...) are committed as the tactic they
          -- suggest, even nested inside a `·` bullet/`<;>` combinator: find
          -- the query-tactic-shaped word in `unit`'s text and splice the
          -- suggestion in at that word (see `findQueryToken`/`spliceToken`'s
          -- doc comments for how this approximates the Python original's
          -- diagnostic-column splicing).
          match tryThisMsg?.bind Text.parseTryThis, findQueryToken unit with
          | some suggestion, some tok =>
            match spliceToken unit tok suggestion with
            | some splicedUnit =>
              match ← runUnitWithTimeout cur splicedUnit timeoutS with
              | .ok snap1 =>
                let errs1 := (snap1.newMessages cur).filter (·.severity == .error)
                if errs1.isEmpty then
                  acc := acc.push (splicedUnit, snap1)
                  msgs := msgs ++ [s!"`{tok}` found: `{suggestion}` (committed in its place)"]
                  cur := snap1
                else
                  acc := acc.push (unit, snap0)
                  msgs := msgs ++ newMsgs0
                  cur := snap0
              | _ =>
                acc := acc.push (unit, snap0)
                msgs := msgs ++ newMsgs0
                cur := snap0
            | none =>
              acc := acc.push (unit, snap0)
              msgs := msgs ++ newMsgs0
              cur := snap0
          | _, _ =>
            acc := acc.push (unit, snap0)
            msgs := msgs ++ newMsgs0
            cur := snap0
          i := i + 1
  let nOk := acc.size
  let newCommitted := acc.toList.reverse ++ s.committed
  let mut sOut := { s with committed := newCommitted }
  let goalsList ← (sOut.committed.head?.map Prod.snd |>.getD sOut.base).ppGoals >>= fun fmts => pure (fmts.map toString)
  let mut complete := false
  if stop == Stop.done && goalsList.isEmpty then
    complete ← completionCheck sOut
    sOut := { sOut with complete }
  let outcome : Outcome := {
    nOk, stop, errUnit?, errText, errMsg, errKind
    goals := goalsList, complete, msgs
    timeoutS := if stop == Stop.timeout then timeoutS else 0 }
  return (outcome, sOut)

/-- Same as `evaluate`, but nothing is committed: immutable snapshots make
speculation trivial (run on `s`, discard the returned session). -/
def speculate (s : Session) (units : Array String) (timeoutS : Float) : IO Outcome := do
  let (out, _) ← evaluate s units timeoutS
  return out

/-- Drop `min count |committed|` snapshots; returns the number actually
dropped. -/
def rollback (s : Session) (count : Nat) : IO (Nat × Session) := do
  let dropped := min count s.committed.length
  return (dropped, { s with committed := s.committed.drop dropped, complete := false })

def goalsOf (s : Session) : IO (List String) := do
  let fmts ← (curSnap s).ppGoals
  return fmts.map toString

def renderGoals (goals : List String) : String :=
  if goals.isEmpty then "goals: 0 — no goals left"
  else s!"goals: {goals.length}\n" ++ String.intercalate "\n\n" goals

def goalDigest (goals : List String) : Nat × String :=
  match goals with
  | [] => (0, "")
  | g :: _ =>
    let concl :=
      match (g.splitOn "\n").find? (·.startsWith "⊢") with
      | some ln => (ln.drop 1).toString.trim
      | none => ""
    (goals.length, concl)

/-- Run `cmd` (a `#`-prefixed query, or any command) against the session's
prefix state; never touches `committed`. -/
def runQuery (s : Session) (cmd : String) : IO String := do
  let budget ← Config.stepTimeout
  match ← runIOWithTimeout (Lean.Elab.IO.processInput cmd (some s.prefixState) {} (some s.file.toString)) budget with
  | none => return s!"query timed out (>{budget}s): {cmd.trim}"
  | some (.error e) => return toString e
  | some (.ok (_, _cmdStateAfter, msgs, _)) =>
    let mut outs : List String := []
    for m in msgs do
      outs := outs ++ [cleanMsg (← m.toString)]
    return if outs.isEmpty then "(no output)" else String.intercalate "\n" outs

/-! ### tactic availability -/

/-- Does `name` parse as a tactic under `env`'s token table (no "unknown
tactic"/parse error)? Cheap and exact -- replaces the prototype's
scratch-document probe (docs/PLAN.md §3). -/
def availableTactics (env : Environment) (names : List String) : List (String × Bool) :=
  names.map fun nm =>
    (nm, match Lean.Parser.runParserCategory env `tactic nm with
      | .ok _ => true
      | .error _ => false)

/-! ### did-you-mean -/

private def splitFragments (s : String) : List String := Id.run do
  let chars := s.toList.toArray
  let n := chars.size
  let mut frags : List String := []
  let mut cur := ""
  let mut i := 0
  while i < n do
    let c := chars[i]!
    if c == '_' then
      if cur ≠ "" then frags := frags ++ [cur]
      cur := ""
    else
      if i > 0 && chars[i - 1]!.isLower && c.isUpper && cur ≠ "" then
        frags := frags ++ [cur]
        cur := c.toString
      else
        cur := cur.push c
    i := i + 1
  if cur ≠ "" then frags := frags ++ [cur]
  return (frags.map (·.toLower)).filter (·.length ≥ 3)

/-- Hard bounds for `suggestNames`'s scan of `env.constants` -- without
these, a fuzzy call against EVERY constant in a Mathlib-sized environment
(several hundred thousand) can take minutes for a single short unknown
identifier (measured: 160s wall for a 1-character `ident`, PutnamBench
`putnam_1972_b2`, 2026-09-06). `maxExamined` bounds the scan itself (most
candidates get skipped by the cheap prefilter below before ever reaching a
fuzzy call); `maxHits` additionally bounds how many candidates are allowed
to survive into `scored`, in case a very generic query matches unusually
many names well before `maxExamined` is reached. -/
def suggestNamesMaxExamined : Nat := 150000
def suggestNamesMaxHits : Nat := 300

/-- Cheap, no-fuzzy-call prefilter deciding whether `cshort` (a candidate's
short name) is even worth fuzzy-matching against `queryLens`/`frags`
(`short`'s own length-list and snake/camel fragments): either its length is
within `[len(q) - 2, len(q) + 4]` for some query `q`, or its lowercase form
contains one of `frags`. A candidate failing both is never fuzzy-matched --
this is what keeps the scan affordable, at the cost of being a strictly
tighter gate than the final inclusion test below (an accepted trade-off:
bounded and fast beats exhaustive and slow). -/
private def suggestNamesPrefilter (cshortLen : Nat) (cshortLower : String) (queryLens : List Nat)
    (frags : List String) : Bool :=
  (queryLens.any fun ql => cshortLen + 2 ≥ ql && cshortLen ≤ ql + 4) ||
  frags.any fun f => containsStr cshortLower f

/-- Near-miss existing constant names for the unknown short name `ident`
(possibly dotted): fuzzy-matched (`Lean.FuzzyMatching.fuzzyMatchScoreWithThreshold?`,
also tried against shrinking prefixes, typo-tolerant) or sharing ≥2
snake_case/CamelCase fragments; ranked by (score, same namespace, shorter
first); internal/private/inaccessible (`✝`) names are skipped. `short`
names under 3 characters return `[]` immediately (too generic to bound
usefully -- everything looks like a near-miss). Otherwise the scan of
`env.constants` is bounded by `suggestNamesMaxExamined`/`suggestNamesMaxHits`
(see their docs) and iterates the map's own `ForIn` instance directly (no
`.toList` materialisation), so a hit budget can `break` out early. -/
def suggestNames (env : Environment) (ident : String) (limit : Nat := 5) : List String := Id.run do
  let parts := (ident.splitOn ".").filter (· ≠ "")
  let short := parts.getLastD ident
  if short.length < 3 then
    return []
  let ns := String.intercalate "." parts.dropLast
  let frags := splitFragments short
  let shrinkCount := min 3 (max 0 (short.length - 2))
  let prefixes := ((List.range shrinkCount).map fun k =>
    String.mk (short.toList.take (short.length - (k + 1)))).filter (· ≠ "")
  let queries := (short :: prefixes).eraseDups
  let queryLens := queries.map String.length
  let mut scored : List (String × Float) := []
  let mut examined : Nat := 0
  let mut hitsCollected : Nat := 0
  for (name, _) in env.constants do
    if examined ≥ suggestNamesMaxExamined || hitsCollected ≥ suggestNamesMaxHits then
      break
    examined := examined + 1
    if name.isInternal then
      continue
    let nmStr := name.toString
    if nmStr == ident || nmStr.endsWith ("." ++ ident) then
      continue
    if containsStr nmStr "✝" || containsStr nmStr "_private" then
      continue
    let cparts := nmStr.splitOn "."
    let cshort := cparts.getLastD nmStr
    let cshortLower := cshort.toLower
    if !suggestNamesPrefilter cshort.length cshortLower queryLens frags then
      continue
    let cns := String.intercalate "." cparts.dropLast
    let mut best : Float := 0.0
    for q in queries do
      match Lean.FuzzyMatching.fuzzyMatchScoreWithThreshold? q cshort with
      | some sc => if sc > best then best := sc
      | none => pure ()
    let hits := frags.countP (fun f => containsStr cshortLower f)
    let need := if frags.length ≥ 2 then 2 else 1
    if best ≤ 0.0 && hits < need && !containsStr cshortLower short.toLower then
      continue
    let sameNs := ns ≠ "" && (cns == ns || cns.endsWith ("." ++ ns))
    let score := best * 2 + Float.ofNat hits * 0.5 + (if sameNs then 1.0 else 0.0)
    scored := scored ++ [(nmStr, score)]
    hitsCollected := hitsCollected + 1
  let ranked := scored.toArray.qsort fun a b =>
    a.2 > b.2 || (a.2 == b.2 && a.1.length < b.1.length)
  return ((ranked.map Prod.fst).toList.eraseDups).take limit

/-! ### goal facts (for `auto_close`'s synthesized candidates) -/

structure GoalFacts where
  arithVars  : List String := []
  posHyps    : List (String × String) := []
  evenPowers : List (String × Nat) := []

private def isZeroLit (e : Expr) : Meta.MetaM Bool := do
  match ← Meta.getNatValue? e with
  | some 0 => return true
  | _ => return false

private def posHypShape (ty : Expr) : Meta.MetaM (Option String) := do
  match ty.getAppFnArgs with
  | (``LT.lt, #[_, _, lhs, rhs]) =>
    if ← isZeroLit lhs then
      return some s!"0 < {← Meta.ppExpr rhs}"
    else
      return none
  | (``LE.le, #[_, _, lhs, rhs]) =>
    if ← isZeroLit lhs then
      return some s!"0 ≤ {← Meta.ppExpr rhs}"
    else
      return none
  | _ => return none

private partial def collectEvenPowers (e : Expr) : Meta.MetaM (List (String × Nat)) := do
  match e with
  | .app .. =>
    match e.getAppFnArgs with
    | (``HPow.hPow, #[_, _, _, _, base, exp]) =>
      let baseAcc ← collectEvenPowers base
      let expAcc ← collectEvenPowers exp
      match ← Meta.getNatValue? exp with
      | some n =>
        if n > 0 && n % 2 == 0 then
          return baseAcc ++ expAcc ++ [(toString (← Meta.ppExpr base), n)]
        else
          return baseAcc ++ expAcc
      | none => return baseAcc ++ expAcc
    | _ =>
      let mut acc ← collectEvenPowers e.getAppFn
      for a in e.getAppArgs do
        acc := acc ++ (← collectEvenPowers a)
      return acc
  | .forallE _ d b _ => return (← collectEvenPowers d) ++ (← collectEvenPowers b)
  | .lam _ d b _ => return (← collectEvenPowers d) ++ (← collectEvenPowers b)
  | .letE _ ty v b _ => return (← collectEvenPowers ty) ++ (← collectEvenPowers v) ++ (← collectEvenPowers b)
  | .mdata _ b => collectEvenPowers b
  | .proj _ _ b => collectEvenPowers b
  | _ => return []

private def isArithTypeName (n : Name) : Bool :=
  n == `Nat || n == `Int || n == `Real || n == `Rat

/-- Facts about the current first goal, read from the `MetaM` local context
(not the printed goal string) -- see docs/PLAN.md's `auto_close` synthesis row. -/
def goalFacts (s : Session) : IO GoalFacts := do
  match (curSnap s).tacticState.goals with
  | [] => return {}
  | g :: _ =>
    let (facts, _) ← (curSnap s).runMetaM <| g.withContext do
      let lctx ← getLCtx
      let mut arithVars : List String := []
      let mut posHyps : List (String × String) := []
      for ldecl in lctx do
        if ldecl.isImplementationDetail || ldecl.userName.hasMacroScopes then
          continue
        let ty ← Meta.whnf ldecl.type
        match ty.getAppFn with
        | .const n _ =>
          if isArithTypeName n && arithVars.length < 4 then
            arithVars := arithVars ++ [ldecl.userName.toString]
        | _ => pure ()
        match ← posHypShape ldecl.type with
        | some desc => posHyps := posHyps ++ [(ldecl.userName.toString, desc)]
        | none => pure ()
      let target ← g.getType
      let evenPowers ← collectEvenPowers target
      pure ({ arithVars, posHyps, evenPowers : GoalFacts })
    return facts

end LeanMcpEvolve.Driver
