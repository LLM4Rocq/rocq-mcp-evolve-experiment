/-
LeanMcpEvolve.Text — parser-driven text layer (docs/PLAN.md §3/§4, phase 2b
deliverable 1). Mirrors the *behaviour* of `prototype-python/src/lean_mcp_evolve/
lean_text.py`, but declaration location and tactic-unit splitting are driven by
Lean's own parser (per docs/PLAN.md §3 "existing Lean constructs to use") instead
of `lean_text.py`'s regex/indentation heuristics. Everything else (comment
stripping, forbidden-token scan, `Try this:` parsing, truncation, import
scanning) is a direct, semantics-preserving port of the Python functions of the
same name, since those are pure text operations that don't need the parser.

No prover interaction happens in this file (`findDecls`/`splitUnits` build a
throwaway `Environment` from the file's own header, exactly as much as needed
to resolve notations/tactics for parsing -- see docs/PLAN.md §3
"declaration location").
-/
import Lean

namespace LeanMcpEvolve.Text

open Lean

/-! ### comments and strings

Direct port of `lean_text.strip_comments`: replace `-- ...`, nested `/- ... -/`
and doc comments with spaces of equal *codepoint* length (so line numbers are
preserved); string literals are left untouched (backslash-escape aware); a
best-effort char-literal skip avoids `'-'`/`'"'` being mistaken for comment/
string delimiters, exactly as the Python version's comment says it does
"well enough for the same purpose". -/

private def isIdentStartChar (c : Char) : Bool :=
  c.isAlpha || c == '_'

private def isIdentContChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'

/-- Does `s` contain `needle` as a substring? (`String` has no `Str.contains`
convenience in this API, so we route through `splitOn`, as the rest of this
file already needs it.) -/
def containsStr (s needle : String) : Bool :=
  (s.splitOn needle).length > 1

/-- Replace comments and doc comments by spaces of equal length; string and
(best-effort) char literals are left untouched. Operates on the codepoint
sequence (`List Char`), so the result has the same *codepoint* count as `src`
(matching the Python implementation's own invariant) -- note this means byte
offsets into the result can drift from `src`'s byte offsets whenever a
replaced comment contained non-ASCII characters; none of the position-bearing
functions below (`findDecls`, `headerEnd`) run this on that path (they only
use it as a decision oracle line-by-line, pairing each cleaned line with the
correspondingly-indexed *original* line to recover exact byte positions -- see
`headerEnd`). -/
def stripComments (src : String) : String := Id.run do
  let chars := src.toList.toArray
  let n := chars.size
  let mut out := chars
  let mut i := 0
  let mut depth := 0
  while i < n do
    let c := chars[i]!
    if depth > 0 then
      if i + 1 < n && chars[i]! == '/' && chars[i+1]! == '-' then
        depth := depth + 1
        out := (out.set! i ' ').set! (i+1) ' '
        i := i + 2
      else if i + 1 < n && chars[i]! == '-' && chars[i+1]! == '/' then
        depth := depth - 1
        out := (out.set! i ' ').set! (i+1) ' '
        i := i + 2
      else
        if c != '\n' then
          out := out.set! i ' '
        i := i + 1
    else if c == '"' then
      -- string literal: keep verbatim, honour backslash escapes
      i := i + 1
      while i < n && chars[i]! != '"' do
        if chars[i]! == '\\' then
          i := i + 1
        i := i + 1
      i := i + 1
    else if c == '\'' && i + 2 < n && chars[i+1]! != '\'' &&
        (chars[i+2]! == '\'' || (chars[i+1]! == '\\' && i + 3 < n && chars[i+3]! == '\'')) then
      -- char literal 'x' or '\n': scan a short window for the closing quote
      let stop := min n (i + 5)
      let mut j := i + 1
      let mut found := false
      while j < stop && !found do
        if chars[j]! == '\'' then found := true
        else j := j + 1
      i := if found then j + 1 else i + 1
    else if i + 1 < n && chars[i]! == '-' && chars[i+1]! == '-' then
      while i < n && chars[i]! != '\n' do
        out := out.set! i ' '
        i := i + 1
    else if i + 1 < n && chars[i]! == '/' && chars[i+1]! == '-' then
      depth := 1
      out := (out.set! i ' ').set! (i+1) ' '
      i := i + 2
    else
      i := i + 1
  return String.mk out.toList

/-! ### forbidden-token scan (verify) -/

private def wordsOutsideStrings (line : String) : Array String := Id.run do
  let chars := line.toList.toArray
  let n := chars.size
  let mut i := 0
  let mut out : Array String := #[]
  while i < n do
    let c := chars[i]!
    if c == '"' then
      i := i + 1
      while i < n && chars[i]! != '"' do
        if chars[i]! == '\\' then i := i + 1
        i := i + 1
      i := i + 1
    else if isIdentStartChar c then
      let mut buf := c.toString
      i := i + 1
      while i < n && isIdentContChar chars[i]! do
        buf := buf.push chars[i]!
        i := i + 1
      out := out.push buf
    else
      i := i + 1
  return out

/-- `(token, 1-based line)` for every forbidden identifier occurring outside
comments and strings. Direct port of `lean_text.scan_forbidden`. -/
def scanForbidden (src : String)
    (tokens : List String := ["sorry", "admit", "axiom", "native_decide", "sorryAx", "ofReduceBool"]) :
    List (String × Nat) := Id.run do
  let clean := stripComments src
  let mut hits : List (String × Nat) := []
  let mut lineNo := 1
  for line in clean.splitOn "\n" do
    for w in wordsOutsideStrings line do
      if tokens.contains w then
        hits := hits ++ [(w, lineNo)]
    lineNo := lineNo + 1
  return hits

/-! ### truncation, imports, header -/

/-- Middle truncation keeping head (2n/3 chars) and tail, matching
`lean_text.truncate` (argument order swapped per the plan's signature:
`n` first). -/
def truncate (n : Nat) (s : String) : String :=
  let len := s.length
  if len <= n then s
  else
    let head := n * 2 / 3
    let tail := n - head
    let chars := s.toList
    let headStr := String.mk (chars.take head)
    let tailStr := String.mk (chars.drop (len - tail))
    headStr ++ s!" … [{len - n} chars elided] … " ++ tailStr

/-- Modules named by the file's leading `import` block (before the first
non-import/non-blank/non-`prelude` line). Direct port of `lean_text.imports_of`. -/
def importsOf (src : String) : List String := Id.run do
  let mut mods : List String := []
  for line in (stripComments src).splitOn "\n" do
    let s := line.trimAscii.toString
    if s.startsWith "import " then
      mods := mods ++ ((s.drop 7).toString.splitOn " ").filter (· ≠ "")
    else if s ≠ "" && !(s.startsWith "prelude") then
      if !mods.isEmpty then
        break
  return mods

/-- Byte position right after the file's import block, i.e. where an injected
`import` line should go. Line-numbering analogue of `lean_text.header_end_line`,
returning a `String.Pos.Raw` instead of a line index. Computed by walking
`src` and `stripComments src` *in lock-step, line by line* (both have the same
line count, since comment-stripping never touches `\n`), so byte offsets are
taken from the *original* line (correct even when a stripped comment contained
non-ASCII text) while the import/blank/prelude test is applied to the cleaned
line. -/
def headerEnd (src : String) : String.Pos.Raw := Id.run do
  let clean := stripComments src
  let srcLines := src.splitOn "\n" |>.toArray
  let cleanLines := clean.splitOn "\n" |>.toArray
  let mut pos : Nat := 0
  let mut lastEnd : Nat := 0
  for i in [0:cleanLines.size] do
    let cl := cleanLines[i]!
    let sl := srcLines.getD i ""
    let s := cl.trimAscii.toString
    let lineEndPos := pos + sl.rawEndPos.byteIdx + 1
    if s.startsWith "import " || s == "prelude" then
      lastEnd := lineEndPos
      pos := lineEndPos
    else if s ≠ "" then
      break
    else
      pos := lineEndPos
  return ⟨lastEnd⟩

/-! ### `Try this:` parsing -/

private def stripLeadingBracketTag (s : String) : String := Id.run do
  if !s.startsWith "[" then
    return s
  let arr := s.toList.toArray
  let n := arr.size
  let mut i := 1
  while i < n && arr[i]! != ']' do
    i := i + 1
  if i >= n then
    return s
  let mut j := i + 1
  while j < n && arr[j]! == ' ' do
    j := j + 1
  return String.mk (arr.toList.drop j)

/-- Extract the suggestion from a `Try this:` info message. Lean renders either
`Try this: exact foo` or `Try this:\n  [apply] exact foo` (only the first
alternative is returned when several are listed). Port of
`lean_text.parse_try_this`. -/
def parseTryThis (msg : String) : Option String := Id.run do
  if !containsStr msg "Try this" then
    return none
  let parts := msg.splitOn "Try this"
  let mut body := String.intercalate "Try this" (parts.drop 1)
  while body.startsWith ":" do
    body := (body.drop 1).toString
  body := body.trim
  for ln0 in body.splitOn "\n" do
    let ln := ln0.trim
    if ln ≠ "" then
      return some (stripLeadingBracketTag ln)
  return none

/-! ### misc -/

/-- Indent every (non-blank) line of every unit by `indent` and join with
newlines. Port of `lean_text.indent_block`. -/
def indentBlock (units : Array String) (indent : String) : String :=
  String.intercalate "\n" (units.toList.flatMap fun u =>
    (u.splitOn "\n").map fun ln => if ln.trim == "" then "" else indent ++ ln)

/-- Leading identifier-ish token (letters, digits, `_ ' . ? !`), or the first
character if the string doesn't start with one. Port of `lean_text.first_word`. -/
def firstWord (s : String) : String := Id.run do
  let t := s.trim
  match t.toList with
  | [] => return ""
  | c0 :: rest =>
    if isIdentStartChar c0 || c0 == '.' then
      let mut buf := c0.toString
      for c in rest do
        if isIdentContChar c || c == '.' then
          buf := buf.push c
        else
          break
      return buf
    else
      return c0.toString

/-! ### declarations -/

/-- How a declaration's value is written, mirroring `lean_text.SplitDecl.style`. -/
inductive DeclStyle where
  | «by»
  | term
  | «sorry»
  | pattern
  | «none»
  deriving Repr, DecidableEq, Inhabited

/-- A located top-level declaration.

Deviation from docs/PLAN.md's pseudo-signature: positions are `String.Pos.Raw`,
not `String.Pos` -- on this toolchain `Syntax.getPos?`/`getTailPos?` already
return `Option String.Pos.Raw` (`String.Pos` is now a *bundled*,
validity-proof-carrying type, see docs/PHASE1_NOTES.md's `String.Slice`
pitfall for the same class of toolchain drift), so `String.Pos.Raw` is what
every other function in this file (and the REPL library) actually hands us. -/
structure Decl where
  /-- `"theorem"`, `"lemma"`, `"def"`, `"example"`, `"instance"`, `"abbrev"`, ...
  (derived from the declaration's own leading keyword; for a
  declaration-shaped macro command such as Mathlib/Batteries's `lemma` this
  falls back to the command's syntax-node name with a trailing `Cmd` dropped). -/
  kind        : String
  /-- As written (may be dotted, e.g. `Foo.bar`). -/
  name        : String
  /-- Namespace-qualified (tracks `namespace`/`section`/`end`). -/
  fullName    : String
  /-- Start of the whole command: attributes, doc comment and a folded
  `set_option ... in` / `open ... in` prefix are all included. -/
  startPos    : String.Pos.Raw
  /-- End of the command. -/
  endPos      : String.Pos.Raw
  /-- 0-based. -/
  startLine   : Nat
  /-- 0-based, inclusive. -/
  endLine     : Nat
  /-- Column of the command's first character. -/
  col         : Nat
  style       : DeclStyle
  /-- Position just before the `:=` of the value (for `by`/`term`/`sorry`
  styles; for `pattern`/`none` styles this is the position of the `declVal`
  node found, if any, else the command's end -- callers refuse to build a
  statement out of those styles, see `statementText`). -/
  stmtEndPos  : String.Pos.Raw
  deriving Repr, Inhabited

/-! ### scope tracking for `findDecls`

`findDecls` parses commands with a fixed `ParserModuleContext` derived only
from the header's imports; it never applies a standalone `open`/`namespace`/
`section`/`end` command's effect to that context, so scoped notations
activated by e.g. `open Nat` (Nat's scoped `!` factorial notation), `open
scoped Real` (`π`) or `open Real` (`∠`) earlier in the file are never
understood when parsing a later declaration (its `declVal` fails to parse,
giving it `DeclStyle.none`). `open X in <decl>` already works, because
Lean's own parser handles the folded `in` form internally
(`Lean.Parser.withOpenDecl`/`withOpen`) -- only *standalone* `open`/
`namespace`/`section`/`end` need this file to replay their effect itself.

The fix below replays exactly the two things that matter for parsing (no
elaboration): (1) which `ScopedEnvExtension`s are *active* -- this lives in
the `Environment` itself, mutated by `Lean.pushScope`/`Lean.popScope`/
`Lean.activateScoped` (see `Lean/ScopedEnvExtension.lean`), which is what
notations/tactics registered with `scoped`/`local` register against; (2) the
`ParserModuleContext`'s `currNamespace`/`openDecls` fields, mirroring
`Lean/Elab/BuiltinCommand.lean`'s `addScope`/`popScopes` and
`Lean/Elab/Open.lean`'s `elabOpenDecl`. Both `Lean.activateScoped` and
`Lean.pushScope`/`Lean.popScope` are generic over any monad with `MonadEnv`
+ `MonadLiftT (ST IO.RealWorld) m`; `ScopeM` below is the smallest such monad
(a bare `Environment` ref), so this reuses those exact library functions
instead of walking `Lean.scopedEnvExtensionsRef` by hand. -/

private abbrev ScopeM := StateRefT Environment IO

private instance : MonadEnv ScopeM where
  getEnv := get
  modifyEnv f := modify f

/-- Run `x` starting from `env`, returning the resulting environment. -/
private def runScopeM (env : Environment) (x : ScopeM Unit) : IO Environment :=
  Prod.snd <$> x.run env

private def pushScopeEnv (env : Environment) : IO Environment :=
  runScopeM env Lean.pushScope

private def popScopeEnv (env : Environment) : IO Environment :=
  runScopeM env Lean.popScope

/-- Activate every registered `ScopedEnvExtension`'s entries for `ns` (what
`open ns`/entering `namespace ns` does to the environment), for each `ns` in
`nss`. -/
private def activateNamespacesEnv (env : Environment) (nss : Array Name) : IO Environment :=
  runScopeM env (nss.forM Lean.activateScoped)

/-- The current namespace as a `Name`, from `findDecls`'s dot-joined
`nsStack` of `namespace`/`section` header strings (`""` for `section`,
filtered out) -- same string this file already builds for `Decl.fullName`,
just parsed back into dotted `Name` components for `ParserModuleContext`/
`Lean.ResolveName.resolveNamespace`. -/
private def currNamespaceName (nsStack : Array String) : Name :=
  let s := String.intercalate "." (nsStack.toList.filter (· ≠ ""))
  if s == "" then .anonymous
  else (s.splitOn ".").foldl (init := Name.anonymous) fun n c => n.mkStr c

/-- Replay a standalone `open` command's effect on `env`/`openDecls` (no
elaboration, so ambiguous/unknown namespaces are silently skipped rather
than erroring): `openSimple`/`openScoped` activate every resolved namespace
(mirroring `Lean.Elab.OpenDecl.elabOpenDecl`, which loops over *all*
resolutions of each identifier, since `open` -- unlike `namespace` -- allows
ambiguity); `openOnly`/`openHiding`/`openRenaming` at least activate the
(unique, if resolvable) namespace named, without tracking the precise
member-level `openDecls` those forms would add (this file never resolves
plain identifiers against `openDecls`, only namespace scoping for parsing,
so that precision buys nothing here). -/
private def applyOpenDecl (env : Environment) (currNamespace : Name) (openDecls : List OpenDecl)
    (decl : Syntax) : IO (Environment × List OpenDecl) := do
  match decl with
  | `(Lean.Parser.Command.openDecl| $nss*) => do
    let mut env := env
    let mut openDecls := openDecls
    for nsId in nss do
      for ns in Lean.ResolveName.resolveNamespace env currNamespace openDecls nsId.getId do
        env ← activateNamespacesEnv env #[ns]
        openDecls := OpenDecl.simple ns [] :: openDecls
    return (env, openDecls)
  | `(Lean.Parser.Command.openDecl| scoped $nss*) => do
    let mut env := env
    for nsId in nss do
      for ns in Lean.ResolveName.resolveNamespace env currNamespace openDecls nsId.getId do
        env ← activateNamespacesEnv env #[ns]
    return (env, openDecls)
  | `(Lean.Parser.Command.openDecl| $nsId ($_ids*)) => do
    let mut env := env
    for ns in Lean.ResolveName.resolveNamespace env currNamespace openDecls nsId.getId do
      env ← activateNamespacesEnv env #[ns]
    return (env, openDecls)
  | `(Lean.Parser.Command.openDecl| $nsId hiding $_ids*) => do
    match Lean.ResolveName.resolveNamespace env currNamespace openDecls nsId.getId with
    | [ns] => return (← activateNamespacesEnv env #[ns], openDecls)
    | _ => return (env, openDecls)
  | `(Lean.Parser.Command.openDecl| $nsId renaming $[$_froms -> $_tos],*) => do
    match Lean.ResolveName.resolveNamespace env currNamespace openDecls nsId.getId with
    | [ns] => return (← activateNamespacesEnv env #[ns], openDecls)
    | _ => return (env, openDecls)
  | _ => return (env, openDecls)

private partial def findFirstOfKinds (kinds : Array Name) (stx : Syntax) : Option Syntax :=
  if kinds.contains stx.getKind then
    some stx
  else
    stx.getArgs.findSome? (findFirstOfKinds kinds)

private def declIdKinds : Array Name := #[``Lean.Parser.Command.declId]
private def declValKinds : Array Name :=
  #[``Lean.Parser.Command.declValSimple, ``Lean.Parser.Command.declValEqns,
    ``Lean.Parser.Command.whereStructInst]

private def lastNameComponent (n : Name) : String :=
  (n.toString.splitOn ".").getLastD n.toString

private def kindStringOf (k : Name) : String :=
  if k == ``Lean.Parser.Command.theorem then "theorem"
  else if k == ``Lean.Parser.Command.definition then "def"
  else if k == ``Lean.Parser.Command.«instance» then "instance"
  else if k == ``Lean.Parser.Command.«axiom» then "axiom"
  else if k == ``Lean.Parser.Command.«example» then "example"
  else if k == ``Lean.Parser.Command.abbrev then "abbrev"
  else if k == ``Lean.Parser.Command.opaque then "opaque"
  else if k == ``Lean.Parser.Command.structure then "structure"
  else if k == ``Lean.Parser.Command.inductive then "inductive"
  else if k == ``Lean.Parser.Command.classInductive then "class inductive"
  else
    let s := lastNameComponent k
    if s.endsWith "Cmd" then s.dropRight 3 else s

/-- `(kindStr, declId?, declVal?)` for a command syntax that looks like a
declaration: either the builtin `Lean.Parser.Command.declaration` node, or (as
a generic fallback, so this needs no special case for Mathlib/Batteries's
`lemma` macro) any command whose subtree contains a `declId`. -/
private def declShapeOf (stx : Syntax) : Option (String × Option Syntax × Option Syntax) :=
  if stx.getKind == ``Lean.Parser.Command.declaration then
    let inner := stx.getArg 1
    some (kindStringOf inner.getKind, findFirstOfKinds declIdKinds inner, findFirstOfKinds declValKinds inner)
  else
    match findFirstOfKinds declIdKinds stx with
    | some declId => some (kindStringOf stx.getKind, some declId, findFirstOfKinds declValKinds stx)
    | none =>
      -- `example` has no `declId` at all; still recognise it via `declaration`
      -- above (this branch only fires for non-`declaration` commands, so an
      -- `example` always goes through the first branch).
      none

/-- Parse `src` with Lean's own parser (header processed for real imports, then
a `parseCommand` loop -- *no elaboration*, so declaration extents are exact but
notations/macros introduced mid-file rather than via `import` are not
understood, matching docs/PLAN.md §3's "declaration location" row) and locate
every top-level declaration. -/
def findDecls (src : String) : IO (Array Decl) := do
  let inputCtx := Lean.Parser.mkInputContext src "<input>"
  let (header, parserState0, _headerMsgs) ← Lean.Parser.parseHeader inputCtx
  let (env0, _procMsgs) ← Lean.Elab.processHeader header {} {} inputCtx
  let fileMap := inputCtx.fileMap
  let mut env := env0
  let mut currNamespace : Name := .anonymous
  let mut openDecls : List OpenDecl := []
  let mut pmctx : Lean.Parser.ParserModuleContext := { env, options := {}, currNamespace, openDecls }
  let mut mps := parserState0
  let mut messages : Lean.MessageLog := {}
  let mut decls : Array Decl := #[]
  let mut nsStack : Array String := #[]
  let mut openDeclsStack : Array (List OpenDecl) := #[]
  let mut more := true
  while more do
    let (stx, mps', messages') := Lean.Parser.parseCommand inputCtx pmctx mps messages
    mps := mps'
    messages := messages'
    if Lean.Parser.isTerminalCommand stx then
      more := false
    else if stx.getKind == ``Lean.Parser.Command.«namespace» then
      nsStack := nsStack.push (stx.getArg 1).getId.toString
      openDeclsStack := openDeclsStack.push openDecls
      env ← pushScopeEnv env
      currNamespace := currNamespaceName nsStack
      env ← activateNamespacesEnv env #[currNamespace]
      pmctx := { pmctx with env, currNamespace, openDecls }
    else if stx.getKind == ``Lean.Parser.Command.«section» then
      -- `section` (even a *named* `section Foo`) does not extend the
      -- current namespace (unlike `namespace Foo`) -- see
      -- `Lean/Elab/BuiltinCommand.lean`'s `elabSection`, which calls
      -- `addScope (isNewNamespace := false) ...`. It still pushes a fresh
      -- scoped-extension frame (so an `open`/`local` inside is undone by
      -- the matching `end`), just without activating anything new.
      nsStack := nsStack.push ""
      openDeclsStack := openDeclsStack.push openDecls
      env ← pushScopeEnv env
      pmctx := { pmctx with env }
    else if stx.getKind == ``Lean.Parser.Command.«end» then
      if nsStack.size > 0 then
        nsStack := nsStack.pop
        env ← popScopeEnv env
        if openDeclsStack.size > 0 then
          openDecls := openDeclsStack.back!
          openDeclsStack := openDeclsStack.pop
        currNamespace := currNamespaceName nsStack
        pmctx := { pmctx with env, currNamespace, openDecls }
    else if stx.getKind == ``Lean.Parser.Command.«open» then
      match stx with
      | `(open $decl:openDecl) =>
        let (env', openDecls') ← applyOpenDecl env currNamespace openDecls decl
        env := env'
        openDecls := openDecls'
        pmctx := { pmctx with env, openDecls }
      | _ => pure ()
    else
      let outerStartPos := stx.getPos?.getD ⟨0⟩
      let endPos := stx.getTailPos?.getD outerStartPos
      -- fold `set_option ... in` / `open ... in` (`Lean.Parser.Command.in`)
      -- into the inner declaration, keeping the outer start position.
      let mut inner := stx
      while inner.getKind == ``Lean.Parser.Command.«in» && inner.getNumArgs ≥ 3 do
        inner := inner.getArg 2
      match declShapeOf inner with
      | none => pure ()
      | some (kindStr, declId?, declVal?) =>
        let name :=
          match declId? with
          | some id => (id.getArg 0).getId.toString
          | none => if kindStr == "example" then "example" else ""
        if name ≠ "" then
          let ns := String.intercalate "." (nsStack.toList.filter (· ≠ ""))
          let fullNameRaw :=
            if name.startsWith "_root_." || ns == "" || kindStr == "example" then name
            else ns ++ "." ++ name
          let fullName := (fullNameRaw.splitOn "_root_.").foldl (init := "") (· ++ ·)
          let (style, stmtEndPos) :=
            match declVal? with
            | none => (.«none», endPos)
            | some dv =>
              if dv.getKind == ``Lean.Parser.Command.declValEqns then
                (.pattern, dv.getPos?.getD endPos)
              else if dv.getKind == ``Lean.Parser.Command.whereStructInst then
                (.«none», dv.getPos?.getD endPos)
              else
                let bodyTerm := dv.getArg 1
                let st :=
                  if bodyTerm.getKind == ``Lean.Parser.Term.byTactic then DeclStyle.«by»
                  else if bodyTerm.getKind == ``Lean.Parser.Term.«sorry» then DeclStyle.«sorry»
                  else DeclStyle.term
                (st, dv.getPos?.getD endPos)
          decls := decls.push {
            kind := kindStr, name, fullName
            startPos := outerStartPos, endPos
            startLine := (fileMap.toPosition outerStartPos).line - 1
            endLine := (fileMap.toPosition endPos).line - 1
            col := (fileMap.toPosition outerStartPos).column
            style, stmtEndPos }
  return decls

/-- Exact full-name match first, then as-written, then unique `.name` suffix. -/
def findDecl (decls : Array Decl) (name : String) : Option Decl :=
  match decls.find? (·.fullName == name) with
  | some d => some d
  | none =>
    match decls.find? (·.name == name) with
    | some d => some d
    | none =>
      let suffix := decls.filter (·.fullName.endsWith ("." ++ name))
      if suffix.size == 1 then suffix[0]? else none

/-- The declaration's text from `startPos` to `stmtEndPos`, right-trimmed, with
`" := by"` appended: the normalised statement fed to the base `sorry`. For
`pattern`/`none` styles this is still computable but meaningless (there is no
single proof position to take over); the driver refuses to `open` such a
declaration. -/
def statementText (src : String) (d : Decl) : String :=
  let raw := String.Pos.Raw.extract src d.startPos d.stmtEndPos
  raw.trimAsciiEnd.toString ++ " := by"

/-- Text after the declaration's `endPos` (the rest of the file). -/
def tailText (src : String) (d : Decl) : String :=
  String.Pos.Raw.extract src d.endPos src.rawEndPos

/-! ### tactic-unit splitting -/

private def leadingSpaces (s : String) : Nat := Id.run do
  let mut n := 0
  for c in s.toList do
    if c == ' ' then n := n + 1 else break
  return n

/-- `textwrap.dedent`-alike: strip the minimum common leading-space count of
every non-blank line from every line (blank lines are normalised to `""`). -/
private def dedent (s : String) : String := Id.run do
  let lines := s.splitOn "\n"
  let nonBlank := lines.filter fun l => l.trim ≠ ""
  if nonBlank.isEmpty then
    return s
  let minIndent := nonBlank.foldl (fun acc l => min acc (leadingSpaces l)) 1000000000
  let newLines := lines.map fun l =>
    if l.trim == "" then "" else String.mk (l.toList.drop minIndent)
  return String.intercalate "\n" newLines

/-- Strip a leading bare `by`, or a leading `by ` prefix on the first line,
normalise CRLF/tabs, then dedent. Port of the corresponding prefix of
`lean_text.split_units`. -/
private def byStripAndDedent (text : String) : String := Id.run do
  let normalized := (text.replace "\r\n" "\n").replace "\t" "  "
  let mut lines := normalized.splitOn "\n"
  while lines ≠ [] && lines.head!.trim == "" do
    lines := lines.tail!
  match lines with
  | [] => pure ()
  | first :: rest =>
    let firstTrim := first.trim
    if firstTrim == "by" then
      lines := rest
    else if firstTrim.startsWith "by " && rest.isEmpty then
      -- the `by ` prefix may not be at column 0; drop just the token
      let idx := (first.splitOn "by ").head!.length
      lines := [String.mk (first.toList.take idx) ++ String.mk (first.toList.drop (idx + 3))]
    else if firstTrim.startsWith "by " then
      -- the `by ` prefix may not be at column 0; drop just the token
      let idx := (first.splitOn "by ").head!.length
      lines := (String.mk (first.toList.take idx) ++ String.mk (first.toList.drop (idx + 3))) :: rest
  return dedent (String.intercalate "\n" lines)

private def bracketDelta (s : String) : Int := Id.run do
  let clean := stripComments s
  let mut d : Int := 0
  let mut inStr := false
  let chars := clean.toList.toArray
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    if inStr then
      if c == '\\' then i := i + 1
      else if c == '"' then inStr := false
    else if c == '"' then
      inStr := true
    else if c == '(' || c == '[' || c == '{' || c == '⟨' then
      d := d + 1
    else if c == ')' || c == ']' || c == '}' || c == '⟩' then
      d := d - 1
    i := i + 1
  return d

/-- Fallback line-based split (used when the parser rejects the text, so that
the driver can still report which unit failed): a unit is a line at base
indentation plus every following line that is indented deeper, starts with
`|` / `<;>`, or is needed to balance open brackets. -/
private def lineBasedSplit (text : String) : Array String := Id.run do
  let mut units : Array String := #[]
  let mut cur : Array String := #[]
  let mut depth : Int := 0
  for line in text.splitOn "\n" do
    if line.trim ≠ "" then
      let indented := line.startsWith " "
      let s := line.trim
      let cont := indented || s.startsWith "|" || s.startsWith "<;>" || depth > 0
      if !cur.isEmpty && cont then
        cur := cur.push line
      else
        if !cur.isEmpty then
          units := units.push (String.intercalate "\n" cur.toList)
        cur := #[line]
      depth := max 0 (depth + bracketDelta line)
  if !cur.isEmpty then
    units := units.push (String.intercalate "\n" cur.toList)
  return units

private def tacticSeqElems (stx : Syntax) : Array Syntax :=
  if stx.getNumArgs == 0 then #[]
  else
    let inner := stx.getArg 0
    if inner.getKind == ``Lean.Parser.Tactic.tacticSeqBracketed then
      if inner.getNumArgs > 1 then (inner.getArg 1).getSepArgs else #[]
    else
      if inner.getNumArgs > 0 then (inner.getArg 0).getSepArgs else #[]

/-- Parse `input` as a `Lean.Parser.Tactic.tacticSeq` under `env`'s token table,
mirroring `Lean.Parser.runParserCategory`'s internals (which only runs named
*categories*, not an arbitrary compound parser like `tacticSeq`). -/
private def runTacticSeqSyntax (env : Environment) (input : String) : Except String Syntax :=
  let p := Lean.Parser.andthenFn Lean.Parser.whitespace Lean.Parser.Tactic.tacticSeq.fn
  let ictx := Lean.Parser.mkInputContext input "<input>"
  let s := p.run ictx { env, options := {} } (Lean.Parser.getTokenTable env) (Lean.Parser.mkParserState input)
  if !s.allErrors.isEmpty then
    .error (s.toErrorMsg ictx)
  else if ictx.atEnd s.pos then
    .ok s.stxStack.back
  else
    .error ((s.mkError "end of input").toErrorMsg ictx)

private def runTacticSeq (env : Environment) (seg : String) : Option (Array String) :=
  match runTacticSeqSyntax env seg with
  | .error _ => none
  | .ok stx =>
    some <| (tacticSeqElems stx).map fun e =>
      let a := e.getPos?.getD ⟨0⟩
      let b := e.getTailPos?.getD a
      String.Pos.Raw.extract seg a b

/-- Split `body` into `(isHashLine, segment)` runs: a `#`-prefixed line is its
own segment, everything between such lines is one segment (possibly further
split by the tactic parser). -/
private def splitOnHashLines (body : String) : List (Bool × String) := Id.run do
  let mut out : List (Bool × String) := []
  let mut buf : List String := []
  for line in body.splitOn "\n" do
    if line.startsWith "#" then
      if !buf.isEmpty then
        out := out ++ [(false, String.intercalate "\n" buf)]
        buf := []
      out := out ++ [(true, line)]
    else
      buf := buf ++ [line]
  if !buf.isEmpty then
    out := out ++ [(false, String.intercalate "\n" buf)]
  return out

/-- Split agent tactic text into units, each one top-level tactic (parser-
driven: `induction n with | zero => .. | succ n ih => ..`, a `·`-bullet with a
nested block, or a bracket-continued `nlinarith [...]` are single units,
because they are single tactics/single top-level sequence elements in Lean's
own grammar -- see docs/PLAN.md's `splitUnits`). Lines starting with `#` are
always their own unit (never fed to the tactic parser, since e.g. `#check` is
not tactic syntax); the driver runs those as commands and never as tactics
(`Driver.evaluate` rejects `#`-units, `Driver.runQuery` handles them). On a
parse error for a segment, falls back to a line-based split for *that segment
only*, so a genuinely broken unit still becomes its own reportable unit rather
than aborting the whole call. -/
def splitUnits (env : Environment) (text : String) : Except String (Array String) :=
  .ok <| Id.run do
    let body := byStripAndDedent text
    if body.trim == "" then
      return #[]
    let mut out : Array String := #[]
    for (isHash, seg) in splitOnHashLines body do
      if isHash then
        out := out.push seg
      else if seg.trim ≠ "" then
        match runTacticSeq env seg with
        | some units => out := out ++ units
        | none => out := out ++ lineBasedSplit seg
    return out

/-! ### placeholder refusal (`sorry`/`sorryAx`/`admit`), used by
`Session.rejectSorryUnit`

A `sorry` (or `sorryAx`/`admit`) closes the current goal without a proof;
this server refuses to execute a tactic UNIT containing one at all (rather
than executing it and reporting PROOF COMPLETE, which is what
`Driver.completionCheck` used to do for Rocq parity -- found on 2026-09-08 to
be a false parity claim: rocq-mcp-evolve's own session server only completes
on a successful `Qed.`, which FAILS after `admit` -- Rocq's `Admitted.` is a
distinct, separate vernacular command the harness never sends via the
tactic-running tools, so there was never a "the Rocq server accepts `admit`
in-session" case to match in the first place). Decided on the unit's own
PARSED syntax (adapted from `Gate.lean`'s `forbiddenHits`/`forbiddenAtoms`/
`forbiddenIdents` walker, kept independent here since `Gate.lean` imports
`Text.lean`, not the other way around), so a `-- sorry` inside a comment or a
`"sorry"` inside a string literal can never trigger it (comments/strings
never make it into `Syntax` at all), while a nested `have h : P := by sorry`
inside a longer unit still does (the walk recurses into every subtree). -/

/-- Atom whose bare value marks a tactic unit as a placeholder. -/
def sorryForbiddenAtoms : List String := ["sorry"]

/-- Identifiers (by bare or last-dot-component text) that spell the same
placeholder directly, bypassing the `sorry` keyword. -/
def sorryForbiddenIdents : List String := ["sorryAx", "admit"]

/-- Walk `stx`'s full subtree for the first atom in `atoms` or identifier (by
bare/last-dot text) in `idents` -- same shape as `Gate.lean`'s
`forbiddenHits`, specialised to return only the first hit (`Session`'s
refusal only needs to know THAT a unit is forbidden and which token, not
every occurrence). -/
partial def syntaxForbiddenHit (atoms idents : List String) (stx : Syntax) : Option String :=
  match stx with
  | .node _ _ args => args.toList.findSome? (syntaxForbiddenHit atoms idents)
  | .atom _ val => if atoms.contains val then some val else none
  | .ident _ _ n _ =>
    let s := n.toString
    let last := (s.splitOn ".").getLastD s
    if idents.contains s then some s
    else if idents.contains last then some last
    else none
  | _ => none

/-- `some tok` when a single tactic UNIT (as produced by `splitUnits`, one
top-level tactic) contains `sorry` (the bare atom) or `sorryAx`/`admit` (an
identifier); `none` when it is clean. Re-parses `unitText` standalone as a
`tacticSeq` and walks the result (see the module note above); falls back to
a `stripComments` + word-boundary scan ONLY when the unit fails to re-parse
on its own -- a `lineBasedSplit` fallback unit (used when the *whole call's*
text already failed the real parser) is not guaranteed to be self-parsing,
but the fallback scan is still comment/string-aware, so the same guarantee
(a commented-out or string-literal `sorry` never triggers) holds either
way. -/
def sorryHit (env : Environment) (unitText : String) : Option String :=
  match runTacticSeqSyntax env unitText with
  | .ok stx => syntaxForbiddenHit sorryForbiddenAtoms sorryForbiddenIdents stx
  | .error _ =>
    let clean := stripComments unitText
    let isCont (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''
    let scan (tok : String) : Bool := Id.run do
      let chars := clean.toList.toArray
      let tokChars := tok.toList.toArray
      let n := chars.size
      let m := tokChars.size
      if m == 0 || m > n then return false
      let mut i := 0
      while i + m ≤ n do
        if chars.extract i (i + m) == tokChars then
          let beforeOk := i == 0 || !isCont chars[i-1]!
          let afterOk := i + m == n || !isCont chars[i+m]!
          if beforeOk && afterOk then return true
        i := i + 1
      return false
    (sorryForbiddenAtoms ++ sorryForbiddenIdents).find? scan

end LeanMcpEvolve.Text
