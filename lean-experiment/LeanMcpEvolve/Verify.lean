/-
Phase 2c (see docs/PLAN.md §6 phase 2c). Port of the Python reference
`prototype-python/src/lean_mcp_evolve/session_server.py`'s
`verify_tool_handler` (whole-project `lake build` + forbidden-token scan),
augmented with the axiom audit that PLAN.md §4's `verify` description calls
for and that the Python prototype could not perform itself (it never runs
inside a Lean process, so it has no way to `collectAxioms`) -- this is the
one place where the Lean port does strictly more than the prototype it
otherwise mirrors verbatim.

Notes on deliberate deviations from the literal task text, each forced by
what this toolchain's core library actually exposes (no Rocq/Coq analogue,
no `Proc.lean` to borrow from -- see the module doc below on `lakeBuild`):

* `forbiddenTokens` is the 4-token list PLAN.md/the task spell out (`sorry`,
  `admit`, `axiom`, `native_decide`), not the Python `FORBIDDEN_TOKENS`
  tuple's full 8 (which adds `sorryAx`, `ofReduceBool`, `implemented_by`,
  `extern` -- names that only appear via meta-programming, not typed by an
  agent, and the first two are exactly what `axiomAudit` independently
  catches through `collectAxioms`).
* The lock (`lakeBuild`'s `acquireLock`/`releaseLock`) is the
  create-rename spin the task explicitly directs when there is no `flock`
  -- there genuinely is none reachable from pure Lean here (no FFI, no
  `Proc.lean` yet). It is best-effort: the exists-check and the rename are
  two syscalls, not one, so a race is possible under true concurrency. The
  staleness clock reuses `IO.monoMsNow` (a monotonic, process-independent
  timer) recorded in the lock file's contents, rather than wall-clock
  `System.FilePath.metadata`, which this core library exposes no "now" for
  outside of statting a file.
* `axiomAudit` always prepends the target root's own
  `lake env printenv LEAN_PATH` to the search path via `initSearchPath`'s
  `sp` argument, rather than only running that subprocess when the
  ambient `LEAN_PATH` is unset: this core library has no public `IO.setEnv`
  to conditionally mutate the process environment, and passing the root's
  path additively (it only ever adds search entries, never removes any)
  is correctness-preserving in both the "unset" and the "already set to
  something else" cases -- notably including our own validation harness,
  which runs under `lake env lean --run` *in this package* so that
  `LeanMcpEvolve.*` resolves, which is a different `LEAN_PATH` than
  whatever project `verify` is asked to check.
-/
import Lean

namespace LeanMcpEvolve.Verify

open System

structure Report where
  ok : Bool
  text : String
  deriving Inhabited

/-! ### small helpers (`String.take`/`.drop` return `String.Slice` on this
toolchain, see docs/PHASE1_NOTES.md pitfalls -- go via `List Char`) -/

/-- Middle truncation keeping head and tail, verbatim port of `T.truncate`. -/
def truncateMid (s : String) (n : Nat) : String :=
  let len := s.length
  if len <= n then s
  else
    let head := n * 2 / 3
    let tail := n - head
    let cs := s.toList
    let headPart := String.ofList (cs.take head)
    let tailPart := String.ofList (cs.drop (len - tail))
    headPart ++ s!" … [{len - n} chars elided] … " ++ tailPart

/-! ### forbidden-token scan -/

/-- The four tokens PLAN.md/the task spell out for `verify`'s scan -- see
the module doc for why this is shorter than Python's `FORBIDDEN_TOKENS`. -/
def forbiddenTokens : List String := ["sorry", "admit", "axiom", "native_decide"]

/-- Replace comments (`-- …`, nested `/- … -/`, doc comments) with spaces of
equal length, preserving offsets/line numbers; string literals (with `\`
escapes) pass through untouched. Verbatim in spirit with `T.strip_comments`,
minus its char-literal (`'-'`) special case, which is irrelevant to token
scanning and not requested by the task. -/
partial def stripComments (src : String) : String :=
  String.ofList (go src.toList 0)
where
  skipStringLiteral : List Char → List Char × List Char
    | [] => ([], [])
    | '\\' :: c2 :: rest =>
      let (lit, rest') := skipStringLiteral rest
      ('\\' :: c2 :: lit, rest')
    | '"' :: rest => (['"'], rest)
    | c :: rest =>
      let (lit, rest') := skipStringLiteral rest
      (c :: lit, rest')
  go : List Char → Nat → List Char
    | [], _ => []
    | c :: rest, depth =>
      if depth > 0 then
        match rest with
        | r0 :: rtail =>
          if c == '/' && r0 == '-' then
            ' ' :: ' ' :: go rtail (depth + 1)
          else if c == '-' && r0 == '/' then
            ' ' :: ' ' :: go rtail (depth - 1)
          else if c == '\n' then
            '\n' :: go rest depth
          else
            ' ' :: go rest depth
        | [] => if c == '\n' then ['\n'] else [' ']
      else
        match c, rest with
        | '"', _ =>
          let (lit, rest') := skipStringLiteral rest
          '"' :: lit ++ go rest' 0
        | '-', (r0 :: rtail) =>
          if r0 == '-' then
            let (skipped, rest2) := rtail.span (· != '\n')
            List.replicate (2 + skipped.length) ' ' ++ go rest2 0
          else
            '-' :: go rest 0
        | '/', (r0 :: rtail) =>
          if r0 == '-' then
            ' ' :: ' ' :: go rtail 1
          else
            '/' :: go rest 0
        | _, _ => c :: go rest 0

private def isWordStart (c : Char) : Bool := c.isAlpha || c == '_'
private def isWordCont (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || c == '\'' || c == '!' || c == '?'

private partial def wordsOfLine (line : String) : List String :=
  go line.toList
where
  go : List Char → List String
    | [] => []
    | c :: rest =>
      if isWordStart c then
        String.ofList (c :: rest.takeWhile isWordCont) :: go (rest.dropWhile isWordCont)
      else go rest

/-- Blank out string-literal contents on a single (already comment-stripped)
line, leaving only the quote marks -- port of `scan_forbidden`'s per-line
`re.sub(r'"(?:\\.|[^"\\])*"', '""', line)`. -/
private partial def blankStringsInLine (line : String) : String :=
  String.ofList (go line.toList)
where
  skip : List Char → List Char
    | [] => []
    | '\\' :: _ :: rest => skip rest
    | '"' :: rest => rest
    | _ :: rest => skip rest
  go : List Char → List Char
    | [] => []
    | '"' :: rest => '"' :: '"' :: go (skip rest)
    | c :: rest => c :: go rest

/-- (token, 1-based line) for every forbidden identifier occurring outside
comments and strings. Port of `T.scan_forbidden`. -/
def scanForbidden (src : String) : List (String × Nat) :=
  let clean := stripComments src
  let lines := clean.splitOn "\n"
  (lines.zipIdx 1).flatMap (fun line1 =>
    let (line, lnNo) := line1
    let blanked := blankStringsInLine line
    (wordsOfLine blanked).filter forbiddenTokens.contains |>.map (fun w => (w, lnNo)))

private def relPath (root p : System.FilePath) : String :=
  let r := root.toString
  let ps := p.toString
  if ps == r then "."
  else (ps.dropPrefix (r ++ "/")).toString

/-- Walk `root` (skipping dot-entries and `build`/`lake-packages`, depth ≤
8), forbidden-token-scanning every `.lean` file; one issue per (file,
token), first occurrence only (matches `verify_tool_handler`'s `seen` set).
-/
partial def forbiddenScan (root : System.FilePath) : IO (List String) :=
  goDir root 0
where
  goDir (d : System.FilePath) (depth : Nat) : IO (List String) := do
    if depth > 8 then return []
    let entries ← (try d.readDir catch _ => pure #[])
    let sorted := entries.qsort (fun a b => decide (a.fileName < b.fileName))
    let mut acc : List String := []
    for e in sorted do
      let name := e.fileName
      unless name.startsWith "." || name == "build" || name == "lake-packages" do
        let p := e.path
        if (← p.isDir) then
          acc := acc ++ (← goDir p (depth + 1))
        else if name.endsWith ".lean" then
          match (← try (some <$> IO.FS.readFile p) catch _ => pure none) with
          | none => pure ()
          | some src =>
            let hits := scanForbidden src
            let mut seen : List String := []
            for hit in hits do
              let (tok, ln) := hit
              unless seen.contains tok do
                seen := seen ++ [tok]
                acc := acc ++ [s!"{relPath root p}:{ln}: forbidden token `{tok}`"]
    return acc

/-! ### `lake build`, serialised by a best-effort lock file -/

private def lockFilePath (root : System.FilePath) : System.FilePath :=
  root / ".lean_mcp_build_lock"

/-- Best-effort mutual exclusion: an atomic create-rename spin with a
stale-lock timeout -- see the module doc for why this, not `flock`, and for
the monotonic-clock staleness trick. -/
private partial def acquireLock (root : System.FilePath) (waitBudgetMs staleMs : Nat) : IO Unit := do
  let lp := lockFilePath root
  let pid ← IO.Process.getPID
  let startMs ← IO.monoMsNow
  let rec loop : IO Unit := do
    let already ← lp.pathExists
    if !already then
      let nowMs ← IO.monoMsNow
      let tmp := root / s!".lean_mcp_build_lock.tmp.{pid}.{nowMs}"
      let claimed ←
        try
          IO.FS.writeFile tmp (toString nowMs)
          IO.FS.rename tmp lp
          pure true
        catch _ =>
          (try IO.FS.removeFile tmp catch _ => pure ())
          pure false
      if claimed then
        return ()
      else
        let elapsed ← IO.monoMsNow
        if elapsed - startMs > waitBudgetMs then return ()
        else
          IO.sleep 200
          loop
    else
      let contentOpt ← (try some <$> IO.FS.readFile lp catch _ => pure none)
      let nowMs ← IO.monoMsNow
      let stale :=
        match contentOpt with
        | none => true
        | some c =>
          match c.trimAscii.copy.toNat? with
          | some t => nowMs - t > staleMs
          | none => true
      if stale then
        (try IO.FS.removeFile lp catch _ => pure ())
        loop
      else
        let elapsed ← IO.monoMsNow
        if elapsed - startMs > waitBudgetMs then return ()
        else
          IO.sleep 200
          loop
  loop

private def releaseLock (root : System.FilePath) : IO Unit :=
  try IO.FS.removeFile (lockFilePath root) catch _ => pure ()

/-- Poll `check` every 200ms until it returns `some` or `deadlineMs`
(`IO.monoMsNow`) passes, never blocking indefinitely on a single call --
the polling discipline docs/PHASE1_NOTES.md found necessary for wall-clock
timeouts on this toolchain. A plain top-level `partial def` (rather than a
local `let rec`) so its non-structural recursion needs no termination
proof and no capture of `IO.Process.Child`'s config-indexed type. -/
private partial def waitUntil (deadlineMs : Nat) (check : IO (Option α)) : IO (Option α) := do
  match (← check) with
  | some v => pure (some v)
  | none =>
    let now ← IO.monoMsNow
    if now >= deadlineMs then pure none
    else
      IO.sleep 200
      waitUntil deadlineMs check

/-- Spawn `lake build` in `root`, capturing combined stdout+stderr, with a
wall-clock timeout and a kill on expiry; serialised across concurrent
`verify` calls via `acquireLock`/`releaseLock`. Local implementation --
`LeanMcpEvolve.Proc` (a sibling module written concurrently, see the task
briefing) is not imported since it is not yet available; Phase 3 may swap
this for `Proc.run`. -/
def lakeBuild (root : System.FilePath) (timeoutS : Float) : IO (Int × Bool × String) := do
  let staleMs := ((timeoutS + 300.0) * 1000.0).toUInt64.toNat
  let waitMs := ((timeoutS + 60.0) * 1000.0).toUInt64.toNat
  acquireLock root waitMs staleMs
  let result ←
    try
      let child ← IO.Process.spawn {
        cmd := "lake", args := #["build"], cwd := some root,
        stdin := .null, stdout := .piped, stderr := .piped, setsid := true }
      let outTask ← IO.asTask child.stdout.readToEnd
      let errTask ← IO.asTask child.stderr.readToEnd
      let deadlineMs := (← IO.monoMsNow) + (timeoutS * 1000.0).toUInt64.toNat
      let exited ← waitUntil deadlineMs (do
        match (← child.tryWait) with
        | some code => pure (some code)
        | none => pure none)
      match exited with
      | some code =>
        let out := match outTask.get with | .ok s => s | .error e => s!"[stdout error: {e}]"
        let err := match errTask.get with | .ok s => s | .error e => s!"[stderr error: {e}]"
        pure (Int.ofNat code.toNat, false, out ++ err)
      | none =>
        (try child.kill catch _ => pure ())
        let graceDeadline := (← IO.monoMsNow) + 5000
        let _ ← waitUntil graceDeadline (do
          if (← child.tryWait).isSome then pure (some ()) else pure none)
        let outFin ← IO.hasFinished outTask
        let errFin ← IO.hasFinished errTask
        let out :=
          if outFin then (match outTask.get with | .ok s => s | .error e => s!"[stdout error: {e}]")
          else "[stdout capture abandoned after kill]"
        let err :=
          if errFin then (match errTask.get with | .ok s => s | .error e => s!"[stderr error: {e}]")
          else "[stderr capture abandoned after kill]"
        pure (-1, true, out ++ err)
    catch e =>
      pure (127, false, s!"exec failed: {e}")
  releaseLock root
  pure result

/-! ### axiom audit -/

def standardAxioms : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]

private def moduleNameOfRelPath (rel : String) : Lean.Name :=
  let noExt :=
    if rel.endsWith ".lean" then (rel.dropSuffix ".lean").toString else rel
  (noExt.splitOn "/").foldl (fun n s => Lean.Name.str n s) Lean.Name.anonymous

/-- Every `.lean` file under `root` outside `.lake`, as a module name
(`Foo/Bar.lean` → `Foo.Bar`); `lakefile.lean` is skipped. -/
partial def collectModules (root : System.FilePath) : IO (List Lean.Name) :=
  goDir root 0
where
  goDir (d : System.FilePath) (depth : Nat) : IO (List Lean.Name) := do
    if depth > 8 then return []
    let entries ← (try d.readDir catch _ => pure #[])
    let sorted := entries.qsort (fun a b => decide (a.fileName < b.fileName))
    let mut acc : List Lean.Name := []
    for e in sorted do
      let name := e.fileName
      unless name.startsWith "." do
        let p := e.path
        if (← p.isDir) then
          acc := acc ++ (← goDir p (depth + 1))
        else if name.endsWith ".lean" && name != "lakefile.lean" then
          acc := acc ++ [moduleNameOfRelPath (relPath root p)]
    return acc

private def runCollectAxioms (env : Lean.Environment) (n : Lean.Name) : IO (Array Lean.Name) :=
  (Lean.collectAxioms n : Lean.CoreM (Array Lean.Name)).toIO'
    { fileName := "<axiom-audit>", fileMap := Lean.FileMap.ofString "" }
    { env := env }

/-- After a successful build: import `modules` into a fresh `Environment`
and, for every constant declared in one of them, `collectAxioms`, flagging
`sorryAx`, `Lean.ofReduceBool` (`native_decide`) and any axiom outside
`propext`/`Classical.choice`/`Quot.sound`. Import failures are caught and
reported as a single issue rather than thrown. Capped at 40 lines. -/
def axiomAudit (root : System.FilePath) (modules : List Lean.Name) : IO (List String) := do
  try
    let pathOut ← IO.Process.output { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"], cwd := some root }
    let extraSp : System.SearchPath :=
      if pathOut.exitCode == 0 then System.SearchPath.parse pathOut.stdout.trimAscii.copy else []
    Lean.initSearchPath (← Lean.findSysroot) extraSp
    let importsArr := (modules.map (fun m => ({ module := m } : Lean.Import))).toArray
    let env ← Lean.importModules importsArr {}
    let mut issues : List String := []
    for nc in env.constants.toList do
      let n := nc.fst
      match env.getModuleIdxFor? n with
      | none => pure ()
      | some idx =>
        match env.header.moduleNames[idx.toNat]? with
        | none => pure ()
        | some mn =>
          if modules.contains mn then
            let axs ← runCollectAxioms env n
            for ax in axs do
              if ax == `sorryAx then
                issues := issues ++ [s!"{n}: depends on sorryAx"]
              else if ax == `Lean.ofReduceBool then
                issues := issues ++ [s!"{n}: depends on Lean.ofReduceBool (native_decide)"]
              else if !(standardAxioms.contains ax) then
                issues := issues ++ [s!"{n}: depends on non-standard axiom {ax}"]
    pure (issues.take 40)
  catch e =>
    pure [s!"axiom-audit: failed to import project modules: {e}"]

/-! ### `verify` -/

/-- `forbiddenScan`, then `lakeBuild`, then (only on a successful build)
`axiomAudit`. Message texts exactly as `verify_tool_handler`'s, extended
with the axiom-audit issue lines PLAN.md's design calls for (see the
module doc). -/
def verify (root : System.FilePath) (buildTimeoutS : Float) : IO Report := do
  let scanIssues ← forbiddenScan root
  let (code, timedOut, output) ← lakeBuild root buildTimeoutS
  let buildOk := code == 0 && !timedOut
  let sorryLines := (output.splitOn "\n").filter (fun l => l.contains "sorry" && l.contains "warning")
  let mut axiomIssues : List String := []
  if buildOk then
    let modules ← collectModules root
    axiomIssues ← axiomAudit root modules
  if scanIssues.isEmpty && buildOk && sorryLines.isEmpty && axiomIssues.isEmpty then
    return { ok := true, text := "VERIFY OK: build clean, no forbidden placeholders. Safe to declare the project done." }
  let allIssues := scanIssues ++ axiomIssues
  let mut body := "VERIFY FAILED — fix before finishing:\n" ++ "\n".intercalate (allIssues.map (fun x => s!"- {x}"))
  if !buildOk then
    body := body ++ (if timedOut then "\n- lake build TIMED OUT" else "\n- lake build FAILS:") ++ "\n" ++ truncateMid output 2500
  else if !sorryLines.isEmpty then
    body := body ++ "\n- lake build warns about sorry:\n" ++ "\n".intercalate (sorryLines.take 20)
  return { ok := false, text := body }

end LeanMcpEvolve.Verify
