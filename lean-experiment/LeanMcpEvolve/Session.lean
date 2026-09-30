/-
LeanMcpEvolve.Session — the nine MCP tools (docs/PLAN.md §4/§5, phase 3
deliverable 1). Port of `prototype-python/src/lean_mcp_evolve/session_server.py`:
every response string, tool description and inputSchema is reproduced verbatim
(the ported test suite asserts on them). This file wires `Driver`/`Text`/
`Hints`/`Verify`/`Mcp` together; it performs no prover interaction of its own
beyond what those modules already expose.

Global session state: a single `IO.Ref (Option Driver.Session)` created in
`Main.lean`'s `main` and threaded into `allTools` (rather than a top-level
`initialize`/`builtin_initialize` ref) -- this keeps `main` free to run under
plain `IO` without relying on initializer-execution ordering across module
boundaries, and it is the ref every handler closure captures.
-/
import LeanMcpEvolve.Mcp
import LeanMcpEvolve.Proc
import LeanMcpEvolve.Text
import LeanMcpEvolve.Driver
import LeanMcpEvolve.Hints
import LeanMcpEvolve.Verify

namespace LeanMcpEvolve.Session

open Lean (Json ToJson toJson)
open LeanMcpEvolve

/-! ### small shared helpers -/

/-- `%g`-style float formatting (Python's `f"{x:g}"`): integral values print
without a decimal point; others print with trailing zeros stripped. Every
timeout value this file ever formats (`LEAN_*_TIMEOUT`) is integral in
practice, so this only needs to be exact on that case and reasonable
otherwise. -/
def fmtG (f : Float) : String := Id.run do
  let s := toString f
  if !Text.containsStr s "." then
    return s
  let mut cs := s.toList
  while cs != [] && cs.getLast! == '0' do
    cs := cs.dropLast
  if cs != [] && cs.getLast! == '.' then
    cs := cs.dropLast
  return String.mk cs

/-- `Text.truncate n (Hints.trimStr s)` -- the common "strip then middle-
truncate" pattern used throughout the Python original's f-strings
(`T.truncate(out.err_text.strip(), N)`). -/
def truncTrim (n : Nat) (s : String) : String :=
  Text.truncate n (Hints.trimStr s)

def isSyntaxKind : Driver.ErrKind → Bool
  | .syntax => true
  | _ => false

def kindStr : Driver.ErrKind → String
  | .unknownRef _ => "unknown_ref"
  | .syntax => "syntax"
  | .other => "other"

/-- `("\n".join(msgs) + "\n") if msgs else ""` -- port of `fmt_msgs`. -/
def fmtMsgs (msgs : List String) : String :=
  if msgs.isEmpty then "" else String.intercalate "\n" msgs ++ "\n"

/-- `str.replace(old, new, 1)` -- Lean's `String.replace` has no count
argument (it replaces every occurrence), so this splits on `old` and rejoins
only the first split point with `new`. -/
def replaceFirst (s old new : String) : String :=
  match s.splitOn old with
  | [] => s
  | [_] => s
  | first :: rest => first ++ new ++ String.intercalate old rest

/-! ### env / workdir / paths (port of the Python module's top-of-file
configuration helpers) -/

def stepTimeout := Driver.Config.stepTimeout
def tryTimeout := Driver.Config.tryTimeout
def autoTimeout := Driver.Config.autoTimeout
def searchTimeout := Driver.Config.searchTimeout
def openTimeout := Driver.Config.openTimeout
def buildTimeout := Driver.Config.buildTimeout

/-- System temp dir fallback for `LEAN_WORKDIR`, mirroring Python's
`tempfile.gettempdir()` (TMPDIR/TEMP/TMP, else `/tmp`). -/
def systemTempDir : IO System.FilePath := do
  for name in ["TMPDIR", "TEMP", "TMP"] do
    match ← IO.getEnv name with
    | some d => if d ≠ "" then return System.FilePath.mk d
    | none => pure ()
  return "/tmp"

/-- `workdir()`: `LEAN_WORKDIR` (created if missing), else the system temp
dir. -/
def workdir : IO System.FilePath := do
  match ← IO.getEnv "LEAN_WORKDIR" with
  | some d =>
    if d ≠ "" then
      let p := System.FilePath.mk d
      (try IO.FS.createDirAll p catch _ => pure ())
      return p
    else
      systemTempDir
  | none => systemTempDir

def envV2 : IO Bool := do
  return (← IO.getEnv "LEAN_ENV_V2") == some "1"

/-- `resolve_path`: absolute paths pass through; relative ones are joined
onto `LEAN_PROJECT_ROOT` (if set and non-empty), else the current directory. -/
def resolvePath (f : String) : IO System.FilePath := do
  let p := System.FilePath.mk f
  if p.isAbsolute then
    return p
  else
    match ← IO.getEnv "LEAN_PROJECT_ROOT" with
    | some r => if r ≠ "" then return (System.FilePath.mk r) / p else return (← IO.currentDir) / p
    | none => return (← IO.currentDir) / p

/-! ### forbidden-token rejection (`reject_forbidden`)

Refusal parity with rocq-mcp-evolve's session server: that server's
`reject_require` refuses exactly ONE thing up front -- a `Require` command,
detected on the PARSED command (not by substring), only when
`ROCQ_ENV_V2=1`. This mirrors that exactly: under `LEAN_ENV_V2=1`, refuse
ONLY `import` -- the literal Lean counterpart of `Require` (Lean cannot
import mid-file either, and the tactics a proof needs are already preloaded
into the session, see `openFile`'s `withPreload`) -- detected on
comment/string-stripped text as a line whose first token is the keyword
`import`, never by a raw substring match.

`sorry`/`sorryAx`/`admit` are a SEPARATE, UNCONDITIONAL refusal
(`rejectSorryUnit` below, not gated by `LEAN_ENV_V2` at all -- see its own
doc comment for why the earlier "executes and is caught after the fact"
design was a false parity claim, corrected 2026-09-08). `native_decide`,
`run_tac`, a custom axiom injected via metaprogramming, etc. still EXECUTE
like any other tactic -- they are not refused up front, but a completion
that depends on any of them (via a disallowed axiom) is now caught
in-session too, by `Driver.completionCheck`'s axiom audit, and, once opted
in, independently re-derived by the out-of-process gate. -/

/-- A line (after `Text.stripComments`) whose first token is the bare keyword
`import` -- the parsed-command analogue of the Rocq server's `Require`
detection (Lean has no mid-file import statement to parse as a command the
way Rocq parses `Require`, so this is line-based rather than syntax-tree-
based, but it is checked against `stripComments`'s output, exactly like
`Text.importsOf`/`Text.headerEnd`, never against the raw text). -/
private def hasImportLine (text : String) : Bool :=
  ((Text.stripComments text).splitOn "\n").any (fun line => Text.firstWord line == "import")

def importNotAllowedMsg : String :=
  "`import` is not allowed: the file's imports are fixed, and the tactic modules preloaded by the session " ++
    "are ALREADY loaded. Work within the loaded libraries."

def rejectForbidden (text : String) : IO (Option String) := do
  if ← envV2 then
    if hasImportLine text then
      return some importNotAllowedMsg
    else
      return none
  else
    return none

/-! ### placeholder refusal (`sorry`/`sorryAx`/`admit`) -- unconditional,
never gated by `LEAN_ENV_V2`

Restored 2026-09-08: `sorry` (or `sorryAx`/`admit`) closes the current goal
without a proof, and an external checker (the standalone gate, or a real
grader) will always reject it -- there is no point ever executing it and
reporting PROOF COMPLETE. The design this replaces claimed this matched
rocq-mcp-evolve's own behaviour ("`sorry` executes and, if it closes the
goal, is reported PROOF COMPLETE -- exactly as the Rocq server accepts
`Admitted.`"); that claim was found FALSE: the Rocq server's session
completion means "a `Qed.` was submitted and succeeded" -- `Qed.` FAILS
outright after an `admit`, and `Admitted.` (which does complete a Rocq
"proof", exactly like this refusal would otherwise let `sorry` do) is a
DISTINCT vernacular command the tactic-running tools never submit on the
agent's behalf. There was never an in-session "placeholder completes"
behaviour on the Rocq side for `sorry` to have parity with. -/

def sorryNotAllowedMsg (tok : String) : String :=
  s!"`{tok}` is not allowed: it closes the goal without a proof and an external checker rejects it — " ++
    "prove the goal or leave it open."

/-- `some (i, tok)` for the first NON-`#`-prefixed unit in `units` (a `#`
query is a command, not a tactic, and is never fed to the tactic parser --
`Driver.evaluate` already refuses it for a different reason) whose parsed
syntax contains a placeholder (see `Text.sorryHit`'s doc comment for how
`i`'s own unit text is decided, including the comment/string-safety
guarantee); `none` when every unit is clean. -/
def firstSorryUnit (env : Lean.Environment) (units : Array String) : Option (Nat × String) := Id.run do
  for i in [0:units.size] do
    let u := units[i]!
    if !(Hints.trimStr u).startsWith "#" then
      match Text.sorryHit env u with
      | some tok => return some (i, tok)
      | none => pure ()
  return none

/-! ### candidate.lean / completion / import echo -/

def writeCandidate (s : Driver.Session) : IO Unit := do
  let wd ← workdir
  IO.FS.writeFile (wd / "candidate.lean") (Driver.candidateText s)

def mathlibTactics : List String :=
  ["linarith", "nlinarith", "norm_num", "positivity", "ring", "ring_nf", "field_simp", "polyrith",
   "aesop", "gcongr", "bound", "push_cast", "norm_cast", "use", "rcases", "obtain", "rintro",
   "simp_all", "tauto", "nontriviality", "cancel_denoms", "interval_cases", "fin_cases", "omega", "decide"]

def coreTactics : List String := ["omega", "decide", "simp_all", "rcases", "obtain", "rintro"]

/-- Whether `tok` occurs in `script` with non-identifier characters (or the
string boundary) on both sides -- port of the Python regex
`(?<![A-Za-z0-9_'])tok(?![A-Za-z0-9_'])`. -/
def wordBoundaryContains (script tok : String) : Bool := Id.run do
  let isCont (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''
  let chars := script.toList.toArray
  let tokChars := tok.toList.toArray
  let n := chars.size
  let m := tokChars.size
  if m == 0 || m > n then
    return false
  let mut i := 0
  while i + m ≤ n do
    if chars.extract i (i + m) == tokChars then
      let beforeOk := i == 0 || !isCont chars[i-1]!
      let afterOk := i + m == n || !isCont chars[i+m]!
      if beforeOk && afterOk then
        return true
    i := i + 1
  return false

def importEcho (s : Driver.Session) : IO String := do
  let echoOff := (← IO.getEnv "LEAN_IMPORT_ECHO") == some "0"
  match s.preloaded with
  | none => return ""
  | some preloadedLine =>
    if echoOff then return ""
    let script := Driver.proofScript s
    let used0 := mathlibTactics.filter (wordBoundaryContains script)
    let used := used0.filter (fun t => !coreTactics.contains t)
    if used.isEmpty then return ""
    return "\nIMPORTANT: this proof uses " ++ String.intercalate ", " used ++
      ". They work in this session because it preloads `" ++ preloadedLine ++
      "`, but your FILE must import it itself or a fresh build fails with \"unknown tactic\". " ++
      "Add after your existing imports:\n" ++ preloadedLine

/-! ### optional out-of-process gate hook (`LEAN_GATE=1`)

An additive layer beyond this process's own in-session checks
(`Driver.completionCheck`'s kernel/axiom audit, `rejectForbidden`'s up-front
text refusals): once those have already passed and `candidate.lean` is
written, optionally hand the candidate to a separate auditor process (built
concurrently as `LeanMcpEvolve.Gate`/`GateMain`, see the task briefing) for a
second opinion. Contract: `gate <candidate> --theorem <name> [--reference
<file>] --project <root>`, stdout `ACCEPTED` or `REJECTED: <reason>`, exit
0/1.

The ONLY fail-open case is `LEAN_GATE` unset -- the hook is then simply not
consulted, exactly as if it did not exist. Once the user has opted in
(`LEAN_GATE=1`) this fails CLOSED: a clean exit 0 with `ACCEPTED` output is
the one accepting outcome, and anything else -- the binary missing, a
non-zero exit without a `REJECTED:` line, a timeout, malformed output -- is
treated as a rejection with reason `gate_unavailable:<detail>`, using the
exact same response shape as a real `REJECTED: <reason>` (so a misconfigured
or broken gate is visible to the agent, not silently bypassed). -/

def gateEnabled : IO Bool := do
  return (← IO.getEnv "LEAN_GATE") == some "1"

/-- `<dir of the running executable>/gate`, overridden by `LEAN_GATE_BIN`. -/
def gateBinPath : IO System.FilePath := do
  let app ← IO.appPath
  let defaultBin := (app.parent.getD (System.FilePath.mk ".")) / "gate"
  match ← IO.getEnv "LEAN_GATE_BIN" with
  | some p => return (if p ≠ "" then System.FilePath.mk p else defaultBin)
  | none => return defaultBin

/-- `some reason` iff the hook is enabled and did not cleanly ACCEPT (see the
module note above): a real `REJECTED: <reason>` from the gate, or a
`gate_unavailable:<detail>` synthesized reason for every other outcome.
`none` only when the hook is disabled OR it exited 0 with `ACCEPTED`. -/
def runGateCheck (s : Driver.Session) (candidate : System.FilePath) : IO (Option String) := do
  if !(← gateEnabled) then
    return none
  let bin ← gateBinPath
  if !(← bin.pathExists) then
    return some s!"gate_unavailable:binary not found at {bin}"
  let mut args : Array String := #[candidate.toString, "--theorem", s.name]
  match ← IO.getEnv "LEAN_TASK_FILE" with
  | some refFile => if refFile ≠ "" then args := args ++ #["--reference", refFile]
  | none => pure ()
  args := args ++ #["--project", s.root.toString]
  let budget ← Driver.Config.openTimeout
  let res ← Proc.run bin.toString args (timeoutS := budget)
  let out := res.output.trim
  if res.timedOut then
    return some s!"gate_unavailable:timeout (>{budget}s)"
  else if res.exitCode == 1 && Text.containsStr out "REJECTED:" then
    let reason := (String.intercalate "REJECTED:" ((out.splitOn "REJECTED:").drop 1)).trim
    return some (if reason.isEmpty then "no reason given" else reason)
  else if res.exitCode == 0 && out.startsWith "ACCEPTED" then
    return none
  else
    return some s!"gate_unavailable:unexpected result (exit {res.exitCode}): {Text.truncate 300 out}"

/-- Write `candidate.lean`, then run the optional gate hook against it.
Returns the message to show the agent AND the session to persist: on
acceptance (hook disabled, absent, or `ACCEPTED`) this is `PROOF COMPLETE...`
with the session unchanged; on `REJECTED: <reason>` the message says so
instead, `candidate.lean` is removed again (the proof is NOT complete, so no
candidate should be left claiming otherwise), and the session has its last
committed unit rolled back (`complete` becomes `false`) so the agent can keep
working. Every caller that used to treat completion as unconditional must use
the RETURNED session, not its own -- only this function knows whether the
gate vetoed it. -/
def completeMsg (s : Driver.Session) : IO (String × Driver.Session) := do
  writeCandidate s
  let wd ← workdir
  let candidate := wd / "candidate.lean"
  match ← runGateCheck s candidate with
  | none =>
    let echo ← importEcho s
    let msg := "PROOF COMPLETE. The finished declaration (replace the theorem's proof in your file with this):\n"
      ++ Text.truncate 3000 (Driver.finishedDeclaration s) ++ echo
    return (msg, s)
  | some reason =>
    let (_, s') ← Driver.rollback s 1
    (try IO.FS.removeFile candidate catch _ => pure ())
    return (s!"candidate REJECTED by the gate: {reason} — the proof is NOT complete", s')

/-! ### hints / suggestions applied to an error body -/

def applyHintAndSuggest (body sentence msg : String) (kind : Driver.ErrKind) (env : Lean.Environment) :
    IO String := do
  let mut b := body
  if ← Hints.hintsOn then
    b := Hints.withHint b sentence msg (kindStr kind)
  if ← Hints.suggestOn then
    match kind with
    | .unknownRef name =>
      let names := Driver.suggestNames env name
      if !names.isEmpty then
        b := b ++ "\nnear-miss names that DO exist: " ++ String.intercalate ", " names
    | _ => pure ()
  return b

/-- Port of `report_outcome`: render a step/check outcome in rocq-mcp-evolve's
phrasing. Also returns the session to persist -- `completeMsg` may veto
completion via the gate hook, in which case this is NOT the `s` passed in
(see `completeMsg`'s doc comment); every other branch returns `s` unchanged. -/
def reportOutcome (s : Driver.Session) (out : Driver.Outcome) : IO (String × Driver.Session) := do
  let bodyMsgs := fmtMsgs out.msgs
  match out.stop with
  | .done =>
    if s.complete then
      let (cm, s') ← completeMsg s
      return (bodyMsgs ++ s!"ok: {out.nOk} tactic(s) committed.\n" ++ cm, s')
    else
      return (bodyMsgs ++ s!"ok: {out.nOk} tactic(s) committed.\n" ++ Driver.renderGoals out.goals, s)
  | .timeout =>
    return (bodyMsgs ++
      s!"{out.nOk} tactic(s) committed, then TIMEOUT (>{fmtG out.timeoutS}s) at `{truncTrim 80 out.errText}` " ++
      s!"— this tactic is too slow here; try something else. (interrupted work cancelled)\n" ++
      Driver.renderGoals out.goals, s)
  | .error =>
    let label := if isSyntaxKind out.errKind then "SYNTAX ERROR" else "ERROR"
    let body0 := bodyMsgs ++
      s!"{out.nOk} tactic(s) committed, then {label} at `{truncTrim 80 out.errText}`:\n{out.errMsg}" ++
      s!"\n\nstate unchanged since last success:\n{Driver.renderGoals out.goals}"
    let b ← applyHintAndSuggest body0 out.errText out.errMsg out.errKind (Driver.sessionEnv s)
    return (b, s)

/-! ### session access (`get_session`) -/

def alreadyComplete : String := "The proof is already COMPLETE. Reply DONE — do not call more tools."

def proofKeywords : List String := ["theorem", "lemma", "example", "instance", "def", "abbrev", "irreducible_def"]

/-- `open_file`'s post-target-resolution half: hand the (already located)
target to `Driver.openFile`, format the "opened ... — proving ..." response,
and install the resulting session in `ref`. -/
def openViaDriver (ref : IO.Ref (Option Driver.Session)) (path : System.FilePath)
    (theorem? : Option String) (prewarm : Bool := false) : IO Mcp.ToolResult := do
  let openT ← openTimeout
  match ← Driver.openFile path theorem? openT prewarm with
  | .error e => return Mcp.textResult e (isError := true)
  | .ok (s, note, headerCached) =>
    let goals ← Driver.goalsOf s
    if goals.isEmpty then
      ref.set (some { s with complete := true })
      return Mcp.textResult s!"opened {path} — {s.name} has no goal after `:= by`?! (nothing to prove)"
        (log := [("import_cached", toJson headerCached)])
    else
      ref.set (some s)
      let whatSuffix := if theorem?.isSome then "" else " (the first unproven declaration)"
      let text := s!"opened {path} — proving {s.name}{whatSuffix}.{note}\n" ++ Driver.renderGoals goals
      return Mcp.textResult text
        (log := [("n_goals", toJson goals.length), ("preloaded", toJson s.preloaded.isSome),
                  ("import_cached", toJson headerCached)])

/-- `open_file(file, theorem)`: resolve the path, then (when a `theorem` name
is given) resolve the target ourselves so a not-found name gets the Python's
exact "theorem X not found in F. Declarations: ..." phrasing -- `Driver.openFile`
alone reports this case differently (it is a Phase-2 module we do not modify;
see the task report for the full list of such wording differences). -/
def openFileImpl (ref : IO.Ref (Option Driver.Session)) (fileArg : String)
    (theorem? : Option String) (prewarm : Bool := false) : IO Mcp.ToolResult := do
  let path ← resolvePath fileArg
  if !(← path.pathExists) then
    return Mcp.textResult s!"no such file: {path}" (isError := true)
  match theorem? with
  | none => openViaDriver ref path none prewarm
  | some thm => do
    let src ← IO.FS.readFile path
    let decls ← Text.findDecls src
    match Text.findDecl decls thm with
    | none =>
      let namesList := decls.toList.filterMap (fun d => if proofKeywords.contains d.kind then some d.fullName else none)
      let joined0 := String.intercalate ", " namesList
      let joined := if joined0.length > 600 then String.mk (joined0.toList.take 600) else joined0
      let namesText := if joined == "" then "(none)" else joined
      return Mcp.textResult s!"theorem {thm} not found in {path}. Declarations: {namesText}" (isError := true)
    | some _ => openViaDriver ref path (some thm) prewarm

/-! ### eager open (`LEAN_TASK_FILE` preset opened at server startup)

`Main.lean` calls `startEagerOpen` once, right after the `Reexec` bootstrap
and before `Mcp.run` starts serving -- when `LEAN_TASK_FILE` is preset and
`LEAN_EAGER_OPEN` is not `"0"`, this kicks the whole `open`/statement-
elaboration cost (an `import Mathlib` run: ~40-70s measured) off into a
background `Task` immediately, so it overlaps with the MCP
`initialize`/`tools/list` handshake instead of landing entirely inside the
FIRST tool call's wall budget (the lazy behaviour this replaces -- see the
Rocq server this port mirrors, which has the statement already executed at
launch). `getSession` and the runtime `open` tool both wait on this task
(`awaitEagerOpen`) instead of ever calling `openFileImpl` on the preset
file a second time concurrently.

Deliberately a plain top-level `initialize` ref, unlike the session ref
itself (see the module doc for why that one is threaded from `Main.lean`
instead) -- this is pure background-open coordination state, not the
request-serving session, exactly the kind of singleton `Mcp.lean`'s own
`logHandleRef`/`seqRef` already use this pattern for. -/
initialize eagerOpenTaskRef : IO.Ref (Option (Task (Except IO.Error Mcp.ToolResult))) ← IO.mkRef none

/-- `LEAN_EAGER_OPEN=0` disables the eager open (default: enabled). -/
def eagerOpenEnabled : IO Bool := do
  match ← IO.getEnv "LEAN_EAGER_OPEN" with
  | some v => return v ≠ "0"
  | none => return true

/-- Start the background eager-open of `LEAN_TASK_FILE`, if any. No-op when
disabled, unset, or already started (never spawns a second concurrent
open) -- safe to call more than once. Logs exactly one `eager_open` JSONL
record (success or failure) once the background task finishes. -/
def startEagerOpen (ref : IO.Ref (Option Driver.Session)) : IO Unit := do
  if !(← eagerOpenEnabled) then
    return ()
  match ← IO.getEnv "LEAN_TASK_FILE" with
  | none => return ()
  | some preset =>
    if preset == "" then
      return ()
    match ← eagerOpenTaskRef.get with
    | some _ => return () -- already started; never race a second open of the preset
    | none =>
      -- `.dedicated`: the open blocks (`Driver.waitTask` polls a nested
      -- elaboration task); on a pool worker it starved that nested task and
      -- the process hung at exit in `lean_finalize_task_manager` (seen in
      -- suite A, 2026-09-07). A dedicated thread leaves the pool free.
      let task ← IO.asTask (prio := .dedicated) (do
        -- Serialize strictly after any background header prewarm (see
        -- `Driver.awaitHeaderPrewarm`'s doc comment) -- two dedicated
        -- threads each independently reaching a fresh `processInput` call
        -- around the same time was observed to deadlock the shared task
        -- pool under load.
        Driver.awaitHeaderPrewarm
        let r ← openFileImpl ref preset none (prewarm := true)
        let ts ← Mcp.wallClockNow
        Mcp.emitLog
          [ ("ts", toJson ts), ("kind", Json.str "eager_open"), ("file", Json.str preset)
          , ("is_error", Json.bool r.isError) ]
        pure r)
      eagerOpenTaskRef.set (some task)

/-- Wait for the in-flight/completed eager-open task, if one was started;
`none` when no eager open was ever started (disabled, or no preset) -- the
caller then falls back to the ordinary lazy path. An `IO.Error` out of the
task itself (the background action throwing rather than returning a normal
`ToolResult`, which `openFileImpl` does not do in practice) is turned into
an error `ToolResult` here rather than propagated, so it can never crash
the server. -/
def awaitEagerOpen : IO (Option Mcp.ToolResult) := do
  match ← eagerOpenTaskRef.get with
  | none => return none
  | some task =>
    match ← IO.wait task with
    | .ok r => return some r
    | .error e => return some (Mcp.textResult s!"eager open of LEAN_TASK_FILE failed: {e}" (isError := true))

/-- `get_session`: the ref if set, else wait on an in-flight eager open (if
one was started), else lazily `open` `LEAN_TASK_FILE` (if preset), else the
pre-open guard error. -/
def getSession (ref : IO.Ref (Option Driver.Session)) : IO (Except Mcp.ToolResult Driver.Session) := do
  match ← ref.get with
  | some s => return .ok s
  | none =>
    let preOpenGuard : Mcp.ToolResult :=
      Mcp.textResult "no proof is open — call the `open` tool with the path of a .lean file first" (isError := true)
    match ← awaitEagerOpen with
    | some r =>
      if r.isError then
        return .error r
      else
        match ← ref.get with
        | some s => return .ok s
        | none => return .error r
    | none =>
      match ← IO.getEnv "LEAN_TASK_FILE" with
      | none => return .error preOpenGuard
      | some preset =>
        if preset == "" then
          return .error preOpenGuard
        else
          let r ← openFileImpl ref preset none
          if r.isError then
            return .error r
          else
            match ← ref.get with
            | some s => return .ok s
            | none => return .error r

/-! ### open -/

def openToolHandler (ref : IO.Ref (Option Driver.Session)) (args : Json) : IO Mcp.ToolResult := do
  -- Serialize with any in-flight eager open of the preset file (never run
  -- two opens concurrently) before doing our own -- possibly different --
  -- open, which must still be able to replace whatever the eager path set.
  let _ ← awaitEagerOpen
  let fileArg := match args.getObjValD "file" with | .str s => s | _ => ""
  let f ← if fileArg ≠ "" then pure fileArg else (IO.getEnv "LEAN_TASK_FILE").map (·.getD "")
  if f == "" then
    return Mcp.textResult "open needs a file argument (no LEAN_TASK_FILE preset is active)" (isError := true)
  let thmArg := match args.getObjValD "theorem" with | .str s => s | _ => ""
  let thm? := if Hints.trimStr thmArg ≠ "" then some thmArg else none
  openFileImpl ref f thm?

def openTool (ref : IO.Ref (Option Driver.Session)) : Mcp.Tool := {
  name := "open"
  description :=
    "Open a Lean 4 .lean file and start (or restart) a proof session on it. Give `file` (absolute path, or " ++
    "relative to the project root). To prove a specific theorem inside the file (e.g. one currently `sorry`), " ++
    "also give `theorem` (its name) — the file is loaded UP TO that statement, its existing proof is ignored, " ++
    "and any EARLIER broken proof is admitted automatically so every theorem is reachable (fix holes in any " ++
    "order). Without `theorem`, the first declaration that errors or uses `sorry` becomes the goal. The project " ++
    "(lakefile) is discovered automatically from the file's location — build it first so imports resolve."
  inputSchema := Json.mkObj [
    ("type", "object"),
    ("properties", Json.mkObj [("file", Json.mkObj [("type", "string")]), ("theorem", Json.mkObj [("type", "string")])]),
    ("required", Json.arr #["file"])
  ]
  handler := openToolHandler ref
}

/-! ### build -/

def buildToolHandler (args : Json) : IO Mcp.ToolResult := do
  match args.getObjValD "file" with
  | .str f =>
    if f == "" then
      return Mcp.textResult "missing required argument: file" (isError := true)
    let path ← resolvePath f
    if !(← path.pathExists) then
      return Mcp.textResult s!"no such file: {path}" (isError := true)
    let buildT ← buildTimeout
    match ← Driver.diagnoseFile path buildT with
    | .error e => return Mcp.textResult e (isError := true)
    | .ok (holes, nOk, outside) =>
      let hs := holes.map (fun h => (h.name, h.what)) ++ outside.map (fun o => ("(file)", o))
      if hs.isEmpty then
        return Mcp.textResult s!"BUILD OK: {nOk} declaration(s), no holes." (log := [("holes", toJson (0 : Nat))])
      else
        let lines := hs.map (fun nw => s!"- {nw.1}: {nw.2}")
        let body := s!"BUILD: {nOk} declaration(s) OK, {hs.length} hole(s):\n" ++ String.intercalate "\n" lines ++
          "\nFix a hole with open{file, theorem:<name>} then prove it."
        return Mcp.textResult body (log := [("holes", toJson hs.length)])
  | _ => return Mcp.textResult "missing required argument: file" (isError := true)

def buildTool : Mcp.Tool := {
  name := "build"
  description :=
    "Diagnose a whole .lean file in ONE call: every declaration is elaborated; a broken proof is admitted so " ++
    "later declarations that depend on it are still checked — you get EVERY broken proof (errors and `sorry`s) " ++
    "at once instead of stopping at the first. Purely diagnostic: does not change the current proof session. " ++
    "Fix holes afterwards with open{file, theorem:<name>}."
  inputSchema := Json.mkObj [
    ("type", "object"),
    ("properties", Json.mkObj [("file", Json.mkObj [("type", "string")])]),
    ("required", Json.arr #["file"])
  ]
  handler := buildToolHandler
}

/-! ### step -/

def stopStr : Driver.Stop → String
  | .done => "done"
  | .error => "error"
  | .timeout => "timeout"

def driverQuery (s : Driver.Session) (cmd : String) : IO String := do
  let out ← Driver.runQuery s cmd
  return s!"`{Hints.trimStr cmd}`:\n{out}"

def stepToolHandler (ref : IO.Ref (Option Driver.Session)) (args : Json) : IO Mcp.ToolResult := do
  match ← getSession ref with
  | .error tr => pure tr
  | .ok s0 =>
  if s0.complete then
    return Mcp.textResult alreadyComplete
  match args.getObjValD "text" with
  | .str text =>
    match ← rejectForbidden text with
    | some bad => return Mcp.textResult bad (isError := true) (log := [("stop", Json.str "forbidden")])
    | none =>
      let env := Driver.sessionEnv s0
      match Text.splitUnits env text with
      | .error _ => return Mcp.textResult "no tactic in `text`" (isError := true)
      | .ok unitsArr0 =>
        if unitsArr0.isEmpty then
          return Mcp.textResult "no tactic in `text`" (isError := true)
        else
          -- A `sorry`/`sorryAx`/`admit` unit is never executed (see
          -- `firstSorryUnit`'s doc comment): truncate the units array right
          -- BEFORE it, so the loop below only ever executes/commits the
          -- clean prefix -- an earlier genuine tactic failure still reports
          -- itself normally (this unit is simply never reached), and the
          -- override just below only fires when the truncated prefix ran
          -- cleanly all the way through without yet completing the proof.
          let sorryTrunc? := firstSorryUnit env unitsArr0
          let unitsArr := match sorryTrunc? with
            | some (k, _) => unitsArr0.take k
            | none => unitsArr0
          let stepT ← stepTimeout
          let t0 ← IO.monoMsNow
          let mut s := s0
          let mut parts : Array String := #[]
          let mut outs : Array Driver.Outcome := #[]
          let mut nQ := 0
          let mut batch : Array String := #[]
          let mut stopped := false
          for u in unitsArr do
            if !stopped then
              if (Hints.trimStr u).startsWith "#" then
                if !batch.isEmpty then
                  let (out, s') ← Driver.evaluate s batch stepT
                  outs := outs.push out
                  s := s'
                  batch := #[]
                let lastNotDone := match outs.back? with
                  | some o => (match o.stop with | .done => false | _ => true)
                  | none => false
                if lastNotDone then
                  stopped := true
                else
                  nQ := nQ + 1
                  parts := parts.push (← driverQuery s u)
              else
                batch := batch.push u
          if !stopped && !batch.isEmpty then
            let (out, s') ← Driver.evaluate s batch stepT
            outs := outs.push out
            s := s'
          let t1 ← IO.monoMsNow
          let proverMs := (t1 - t0).toFloat
          let nOk := (outs.toList.map (·.nOk)).foldl (· + ·) 0
          let allMsgs := outs.toList.flatMap (·.msgs)
          let finalOut0 : Driver.Outcome ←
            match outs.back? with
            | some last => pure { last with nOk := nOk, msgs := allMsgs }
            | none => do
              let goals ← Driver.goalsOf s
              pure ({ nOk := 0, stop := .done, goals := goals, complete := s.complete : Driver.Outcome })
          let (finalOut, sorryRejected) :=
            match sorryTrunc? with
            | some (k, tok) =>
              if finalOut0.stop == Driver.Stop.done && !finalOut0.complete then
                ({ finalOut0 with
                    stop := .error, errUnit? := some finalOut0.nOk, errText := unitsArr0[k]!,
                    errMsg := sorryNotAllowedMsg tok, errKind := .other, complete := false }, true)
              else (finalOut0, false)
            | none => (finalOut0, false)
          let qnote := if nQ > 0 then s!" ({nQ} query command(s) executed, not committed)" else ""
          let (body0, s') ← reportOutcome s finalOut
          s := s'
          let body :=
            if nQ > 0 then
              String.intercalate "\n" parts.toList ++ "\n" ++
                replaceFirst body0 "tactic(s) committed." s!"tactic(s) committed{qnote}."
            else body0
          ref.set (some s)
          let stopField := if sorryRejected then "sorry_rejected" else stopStr finalOut.stop
          return Mcp.textResult body
            (log := [("prover_ms", toJson proverMs), ("tactics_ok", toJson nOk),
                     ("stop", Json.str stopField), ("n_goals", toJson finalOut.goals.length),
                     ("complete", toJson s.complete)])
  | _ =>
    let sentKeys := match args with | Json.obj kv => kv.foldl (fun acc k _ => acc ++ [k]) [] | _ => []
    let suffix :=
      if sentKeys.isEmpty then ""
      else s!" (got `{String.intercalate "`, `" sentKeys}` — this tool takes `text`)"
    return Mcp.textResult ("missing required argument: text" ++ suffix) (isError := true)

def stepTool (ref : IO.Ref (Option Driver.Session)) : Mcp.Tool := {
  name := "step"
  description :=
    "Execute one or more Lean 4 tactics in the live proof session (one tactic per line: `intro x`, " ++
    "`nlinarith [sq_nonneg (x - 1)]`, `· simp` bullets, multi-line `induction n with | zero => .. | succ n ih => ..`), " ++
    "or query commands like `#check Nat.add_comm` / `#print axioms foo`. Tactics run in order; each success is " ++
    "committed permanently. On the first failure execution stops: earlier tactics of this call STAY committed, " ++
    "the error is reported, and the goal state shown is the one after the last success. Search tactics " ++
    "(`exact?`, `apply?`, `rw?`, `simp?`) are committed as the tactic they find. The proof is complete when no goals remain."
  inputSchema := Json.mkObj [
    ("type", "object"),
    ("properties", Json.mkObj [
      ("text", Json.mkObj [
        ("type", "string"),
        ("description", "Lean tactics to execute, one per line (or `#` query commands)")])]),
    ("required", Json.arr #["text"])
  ]
  handler := stepToolHandler ref
}

/-! ### rollback -/

def rollbackToolHandler (ref : IO.Ref (Option Driver.Session)) (args : Json) : IO Mcp.ToolResult := do
  match ← getSession ref with
  | .error tr => pure tr
  | .ok s0 =>
    let count : Nat :=
      match (args.getObjValD "count").getInt? with
      | .ok n => if n > 0 then n.toNat else 1
      | .error _ => 1
    let (dropped, s1) ← Driver.rollback s0 count
    ref.set (some s1)
    let goals ← Driver.goalsOf s1
    return Mcp.textResult
      s!"rolled back {dropped} tactic(s). {s1.committed.length} remain committed.\n{Driver.renderGoals goals}"
      (log := [("rolled_back", toJson dropped)])

def rollbackTool (ref : IO.Ref (Option Driver.Session)) : Mcp.Tool := {
  name := "rollback"
  description := "Undo the last N committed tactics and show the goal state you are back to."
  inputSchema := Json.mkObj [
    ("type", "object"),
    ("properties", Json.mkObj [
      ("count", Json.mkObj [("type", "integer"), ("description", "How many tactics to undo (default 1)")])]),
    ("required", Json.arr #[])
  ]
  handler := rollbackToolHandler ref
}

/-! ### try -/

def tryLine (i : Nat) (cand : String) (out : Driver.Outcome) (committedIdx : Int) : String :=
  let tag := s!"[{i+1}] `{Text.truncate 60 ((Hints.trimStr cand).replace "\n" " ⏎ ")}` — "
  match out.stop with
  | .done =>
    let status :=
      if out.complete then "OK, closes ALL goals"
      else
        let (n, concl) := Driver.goalDigest out.goals
        if n > 0 then s!"OK, {n} goal(s) left; next: {Text.truncate 120 concl}" else "OK, no goals left"
    tag ++ status ++ (if committedIdx == (i : Int) then "  << COMMITTED" else "  (not committed)")
  | .timeout =>
    tag ++ (if out.nOk > 0 then s!"({out.nOk} tactic(s) would pass) " else "") ++
      s!"timeout (>{fmtG out.timeoutS}s) at `{truncTrim 60 out.errText}`"
  | .error =>
    let label := if isSyntaxKind out.errKind then "syntax error" else "error"
    tag ++ (if out.nOk > 0 then s!"({out.nOk} tactic(s) would pass) " else "") ++
      s!"{label} at `{truncTrim 60 out.errText}`: {Text.truncate 200 out.errMsg}"

def tryToolHandler (ref : IO.Ref (Option Driver.Session)) (args : Json) : IO Mcp.ToolResult := do
  match ← getSession ref with
  | .error tr => pure tr
  | .ok s0 =>
  if s0.complete then
    return Mcp.textResult alreadyComplete
  let rawCands : List Json := match args.getObjValD "candidates" with | Json.arr a => a.toList | _ => []
  let cands0 := rawCands.filterMap (fun j => match j with
    | .str s => if Hints.trimStr s ≠ "" then some s else none
    | _ => none)
  let cands := cands0.take 8
  if cands.isEmpty then
    return Mcp.textResult "candidates must be a non-empty array of strings" (isError := true)
  let commitFirst := match args.getObjValD "commit" with | Json.str "none" => false | _ => true
  let env := Driver.sessionEnv s0
  let tryT ← tryTimeout
  let t0 ← IO.monoMsNow
  let mut outcomes : Array Driver.Outcome := #[]
  let mut unitLists : Array (Array String) := #[]
  let mut anySorryRejected := false
  for cand in cands do
    match ← rejectForbidden cand with
    | some bad =>
      outcomes := outcomes.push
        ({ nOk := 0, stop := .error, errUnit? := some 0, errText := cand, errMsg := bad, errKind := .other
          : Driver.Outcome })
      unitLists := unitLists.push #[]
    | none =>
      let units? := match Text.splitUnits env cand with | .ok u => u | .error _ => #[]
      if units?.isEmpty then
        outcomes := outcomes.push
          ({ nOk := 0, stop := .error, errUnit? := some 0, errText := cand, errMsg := "empty script", errKind := .other
            : Driver.Outcome })
        unitLists := unitLists.push #[]
      else
        -- A candidate containing a `sorry`/`sorryAx`/`admit` unit anywhere
        -- is rejected WHOLESALE (never speculated/evaluated, never
        -- committed) -- see `firstSorryUnit`'s doc comment. Unlike
        -- `step`/`check`, `try`'s candidates are not incrementally
        -- committed within themselves, so there is no "good prefix" to
        -- preserve here: the whole candidate is just one more rejected
        -- option among the up-to-8 tried.
        match firstSorryUnit env units? with
        | some (_, tok) =>
          anySorryRejected := true
          outcomes := outcomes.push
            ({ nOk := 0, stop := .error, errUnit? := some 0, errText := cand, errMsg := sorryNotAllowedMsg tok,
               errKind := .other : Driver.Outcome })
          unitLists := unitLists.push #[]
        | none =>
          let out ← Driver.speculate s0 units? tryT
          outcomes := outcomes.push out
          unitLists := unitLists.push units?
  let mut committedIdx : Int := -1
  let mut s := s0
  if commitFirst then
    let mut found := false
    for i in [0:outcomes.size] do
      if !found then
        let out := outcomes[i]!
        if out.stop == .done then
          found := true
          let (final, s') ← Driver.evaluate s0 (unitLists[i]!) tryT
          if final.stop == .done then
            committedIdx := (i : Int)
            outcomes := outcomes.set! i final
            s := s'
  let t1 ← IO.monoMsNow
  let proverMs := (t1 - t0).toFloat
  let mut seenHints : List String := []
  let mut suggested := false
  let mut lines : Array String := #[]
  let hintsOn ← Hints.hintsOn
  let suggestOn ← Hints.suggestOn
  for i in [0:cands.length] do
    let cand := cands[i]!
    let out := outcomes[i]!
    let mut line := tryLine i cand out committedIdx
    if out.stop == .error then
      if hintsOn then
        match Hints.hintFor out.errText out.errMsg (kindStr out.errKind) with
        | some h =>
          if !seenHints.contains h then
            seenHints := seenHints ++ [h]
            line := line ++ "\n    hint: " ++ h
        | none => pure ()
      if !suggested then
        match out.errKind with
        | .unknownRef name =>
          if suggestOn then
            let names := Driver.suggestNames env name
            if !names.isEmpty then
              suggested := true
              line := line ++ "\nnear-miss names that DO exist: " ++ String.intercalate ", " names
        | _ => pure ()
    lines := lines.push line
  let mut tailText := ""
  if s.complete then
    let (cm, s') ← completeMsg s
    s := s'
    tailText := "\n" ++ cm
  else if committedIdx ≥ 0 then
    let goals ← Driver.goalsOf s
    tailText := "\nafter commit:\n" ++ Driver.renderGoals goals
  else
    tailText := "\nnothing committed; state unchanged."
  ref.set (some s)
  let stopLog := if anySorryRejected then [("stop", Json.str "sorry_rejected")] else []
  return Mcp.textResult (String.intercalate "\n" lines.toList ++ tailText)
    (log := [("prover_ms", toJson proverMs), ("n_candidates", toJson cands.length),
             ("committed_idx", toJson committedIdx), ("complete", toJson s.complete)] ++ stopLog)

def tryTool (ref : IO.Ref (Option Driver.Session)) : Mcp.Tool := {
  name := "try"
  description :=
    "Try up to 8 candidate tactic scripts SPECULATIVELY against the current state, in order. Each candidate is " ++
    "evaluated independently from the same state. The first candidate that fully succeeds is COMMITTED (like " ++
    "step); all others are just reported with what they would do. Use this to test several ideas in one call " ++
    "instead of one step per idea."
  inputSchema := Json.mkObj [
    ("type", "object"),
    ("properties", Json.mkObj [
      ("candidates", Json.mkObj [
        ("type", "array"),
        ("items", Json.mkObj [("type", "string")]),
        ("description",
          "Candidate scripts (each one or more tactics, e.g. \"nlinarith [sq_nonneg (x - 1)]\" or " ++
          "\"intro x\\nfield_simp\\nring\")")]),
      ("commit", Json.mkObj [
        ("type", "string"),
        ("enum", Json.arr #["first_success", "none"]),
        ("description", "Whether to commit the first fully-successful candidate (default first_success)")])]),
    ("required", Json.arr #["candidates"])
  ]
  handler := tryToolHandler ref
}

/-! ### auto_close: finisher portfolio -/

def portfolioBase : List String :=
  ["rfl", "trivial", "simp", "omega", "decide", "norm_num", "linarith", "nlinarith", "positivity",
   "ring", "field_simp\nring", "simp_all", "aesop", "tauto", "bound", "gcongr", "norm_num [*]",
   "intros\nlinarith", "intros\nnlinarith"]

def searchCloser : String := "exact?"

def portfolio : IO (List String) := do
  let mut base := portfolioBase
  match ← IO.getEnv "LEAN_PORTFOLIO_EXTRA" with
  | some extra =>
    if extra ≠ "" then
      base := base ++ ((extra.splitOn "\n").filter (fun x => Hints.trimStr x ≠ ""))
  | none => pure ()
  let autoSearchOff := (← IO.getEnv "LEAN_AUTO_SEARCH") == some "0"
  if !autoSearchOff then
    base := base ++ [searchCloser]
  return base

def runFinishers (s0 : Driver.Session) : IO (String × Float × Option String × Driver.Session) := do
  let t0 ← IO.monoMsNow
  let port ← portfolio
  let env := Driver.sessionEnv s0
  let names :=
    ((port.flatMap (·.splitOn "\n")).filterMap
      (fun u => let w := Text.firstWord u; if w == "" then none else some w)).eraseDups.toArray.qsort (· < ·) |>.toList
  let availList := Driver.availableTactics env names
  let avail (nm : String) : Bool := (availList.lookup nm).getD true
  let cands0 := port.filter (fun c => (c.splitOn "\n").all (fun u => avail (Text.firstWord u)))
  let gf ← Driver.goalFacts s0
  let auto2 ← Hints.auto2On
  let synthRaw := Hints.synthCandidates
    ({ arithVars := gf.arithVars, posHyps := gf.posHyps, evenPowers := gf.evenPowers } : Hints.GoalFacts) auto2
  let synth := if avail "nlinarith" then synthRaw else []
  let cands := (cands0.filter (· ≠ searchCloser)) ++ synth ++ (if cands0.contains searchCloser then [searchCloser] else [])
  let goals0 ← Driver.goalsOf s0
  let before := goals0.length
  let autoT ← autoTimeout
  let searchT ← searchTimeout
  let mut s := s0
  let mut tried : List String := []
  let mut winnerText? : Option String := none
  for cand in cands do
    if winnerText?.isNone then
      let tmo := if cand == searchCloser then searchT else (if cand.length > 40 then autoT * 2 else autoT)
      match Text.splitUnits env cand with
      | .error _ => tried := tried ++ [cand]
      | .ok units =>
        let (out, s') ← Driver.evaluate s units tmo
        if out.stop == .done && (out.complete || out.goals.length < before) then
          let n := units.size
          let winComm := ((s'.committed.take n).reverse).map Prod.fst
          winnerText? := some (String.intercalate "\n" winComm)
          s := s'
        else
          if out.nOk > 0 then
            let (_, sBack) ← Driver.rollback s' out.nOk
            s := sBack
          else
            s := s'
          tried := tried ++ [cand]
  let t1 ← IO.monoMsNow
  let proverMs := (t1 - t0).toFloat
  match winnerText? with
  | some wt =>
    if s.complete then
      let (cm, s') ← completeMsg s
      s := s'
      return (s!"`{wt}` closes it — COMMITTED.\n" ++ cm, proverMs, some wt, s)
    else
      let goals ← Driver.goalsOf s
      return (s!"`{wt}` closes the current goal — COMMITTED.\n" ++ Driver.renderGoals goals, proverMs, some wt, s)
  | none =>
    let namesTried := String.intercalate " " (tried.map Text.firstWord)
    let body :=
      s!"no finisher applies (tried {tried.length}: {namesTried}). Do structural work " ++
      s!"(intro / rcases / have a helper fact) and try again."
    return (body, proverMs, none, s)

def autoCloseToolHandler (ref : IO.Ref (Option Driver.Session)) (_args : Json) : IO Mcp.ToolResult := do
  match ← getSession ref with
  | .error tr => pure tr
  | .ok s0 =>
  if s0.complete then
    return Mcp.textResult alreadyComplete
  let goals0 ← Driver.goalsOf s0
  if goals0.isEmpty then
    return Mcp.textResult "no goal open — nothing to close. Use open{file, theorem?} to start one."
  let (body, proverMs, winner?, s1) ← runFinishers s0
  ref.set (some s1)
  return Mcp.textResult body
    (log := [("prover_ms", toJson proverMs), ("closed", toJson winner?.isSome),
             ("winner", Json.str (winner?.getD "")), ("complete", toJson s1.complete)])

def autoCloseTool (ref : IO.Ref (Option Driver.Session)) : Mcp.Tool := {
  name := "auto_close"
  description :=
    "Run the standard finishing portfolio against the CURRENT goal in one call: rfl, trivial, simp, omega, " ++
    "decide, norm_num, linarith, nlinarith, positivity, ring, field_simp+ring, aesop, tauto, bound, gcongr — plus " ++
    "mechanically synthesized square-nonnegativity / product hints for nlinarith, and a library search (`exact?`) " ++
    "last. If one fully succeeds it is committed automatically. Call this first on every new goal before " ++
    "hand-crafting tactics; if it fails, do structural work (intro/rcases/have) and call it again on the simplified goal."
  inputSchema := Json.mkObj [("type", "object"), ("properties", Json.mkObj [])]
  handler := autoCloseToolHandler ref
}

/-! ### check -/

def checkToolHandler (ref : IO.Ref (Option Driver.Session)) (args : Json) : IO Mcp.ToolResult := do
  match ← getSession ref with
  | .error tr => pure tr
  | .ok s0 =>
  if s0.complete then
    return Mcp.textResult "The proof is already COMPLETE. Reply DONE."
  match args.getObjValD "script" with
  | .str script =>
    match ← rejectForbidden script with
    | some bad => return Mcp.textResult bad (isError := true)
    | none =>
      let env := Driver.sessionEnv s0
      let units0 := match Text.splitUnits env script with | .ok u => u | .error _ => #[]
      if units0.isEmpty then
        return Mcp.textResult "empty script" (isError := true)
      else
        -- Same truncate-before-the-offending-unit semantics as `step` --
        -- see `firstSorryUnit`'s doc comment.
        let sorryTrunc? := firstSorryUnit env units0
        let units? := match sorryTrunc? with
          | some (k, _) => units0.take k
          | none => units0
        let nDiscarded := s0.committed.length
        let (_, sReset) ← Driver.rollback s0 nDiscarded
        let stepT ← stepTimeout
        let t0 ← IO.monoMsNow
        let (out0, s1_0) ← Driver.evaluate sReset units? stepT
        let mut s1 := s1_0
        let t1 ← IO.monoMsNow
        let proverMs := (t1 - t0).toFloat
        let (out, sorryRejected) :=
          match sorryTrunc? with
          | some (k, tok) =>
            if out0.stop == Driver.Stop.done && !out0.complete then
              ({ out0 with
                  stop := .error, errUnit? := some out0.nOk, errText := units0[k]!,
                  errMsg := sorryNotAllowedMsg tok, errKind := .other, complete := false }, true)
            else (out0, false)
          | none => (out0, false)
        let mut body0 := ""
        match out.stop with
        | .done =>
          if s1.complete then
            let (cm, s') ← completeMsg s1
            s1 := s'
            body0 := cm
          else
            body0 := s!"script accepted but the proof is not closed ({out.nOk} tactic(s) committed).\n{Driver.renderGoals out.goals}"
        | .timeout =>
          let (txt, s') ← reportOutcome s1 out
          s1 := s'
          body0 := txt
        | .error =>
          let label := if isSyntaxKind out.errKind then "SYNTAX ERROR" else "ERROR"
          let b0 :=
            s!"{fmtMsgs out.msgs}{out.nOk} tactic(s) committed, then {label} at `{truncTrim 80 out.errText}`:\n{out.errMsg}" ++
            s!"\n\nyou are now AT that point in the proof — repair from here (step/try/auto_close) or rollback and resubmit:\n{Driver.renderGoals out.goals}"
          body0 ← applyHintAndSuggest b0 out.errText out.errMsg out.errKind (Driver.sessionEnv s1)
        let body :=
          if nDiscarded > 0 then
            s!"(fresh attempt: {nDiscarded} previously committed tactic(s) discarded)\n" ++ body0
          else body0
        ref.set (some s1)
        let stopLog := if sorryRejected then [("stop", Json.str "sorry_rejected")] else []
        return Mcp.textResult body
          (log := [("prover_ms", toJson proverMs), ("tactics_ok", toJson out.nOk),
                   ("discarded", toJson nDiscarded), ("complete", toJson s1.complete)] ++ stopLog)
  | _ => return Mcp.textResult "missing required argument: script" (isError := true)

def checkTool (ref : IO.Ref (Option Driver.Session)) : Mcp.Tool := {
  name := "check"
  description :=
    "Check a COMPLETE proof attempt in one call: pass the entire tactic script (everything after `:= by`; do NOT " ++
    "repeat the file/statement — the session already contains them). On success the proof is done. On failure, " ++
    "everything up to the first bad tactic stays committed and you see the error plus the live goal there, so " ++
    "you can repair with step/try/auto_close or resubmit a fixed script after rollback."
  inputSchema := Json.mkObj [
    ("type", "object"),
    ("properties", Json.mkObj [
      ("script", Json.mkObj [
        ("type", "string"),
        ("description", "Complete tactic script (the body of the `by` block)")])]),
    ("required", Json.arr #["script"])
  ]
  handler := checkToolHandler ref
}

/-! ### state -/

def stateToolHandler (ref : IO.Ref (Option Driver.Session)) (_args : Json) : IO Mcp.ToolResult := do
  match ← getSession ref with
  | .error tr => pure tr
  | .ok s =>
    let proof := if s.committed.isEmpty then "(nothing committed yet)" else Driver.proofScript s
    let goals ← Driver.goalsOf s
    return Mcp.textResult
      (s!"proving {s.name} in {s.file}\ncommitted proof:\n{proof}\n" ++
        (if s.complete then "PROOF COMPLETE.\n" else "") ++ Driver.renderGoals goals)

def stateTool (ref : IO.Ref (Option Driver.Session)) : Mcp.Tool := {
  name := "state"
  description := "Show the current proof state (all open goals) and the committed proof so far."
  inputSchema := Json.mkObj [("type", "object"), ("properties", Json.mkObj [])]
  handler := stateToolHandler ref
}

/-! ### verify -/

def verifyRoot (ref : IO.Ref (Option Driver.Session)) : IO System.FilePath := do
  match ← IO.getEnv "LEAN_PROJECT_ROOT" with
  | some r =>
    if r ≠ "" then return System.FilePath.mk r
    else
      match ← ref.get with
      | some s => return s.root
      | none => IO.currentDir
  | none =>
    match ← ref.get with
    | some s => return s.root
    | none => IO.currentDir

def verifyToolHandler (ref : IO.Ref (Option Driver.Session)) (_args : Json) : IO Mcp.ToolResult := do
  let root ← verifyRoot ref
  let buildT ← buildTimeout
  let report ← Verify.verify root buildT
  return Mcp.textResult report.text (log := [("ok", toJson report.ok)])

def verifyTool (ref : IO.Ref (Option Driver.Session)) : Mcp.Tool := {
  name := "verify"
  description :=
    "Verify the whole project BEFORE declaring it done: runs a clean `lake build` at the project root and scans " ++
    "every .lean file for tokens that reviewers/graders reject even when the build passes (sorry, admit, axiom, " ++
    "native_decide). Use `sorry` freely as temporary scaffolding while working — then call verify and fix " ++
    "everything it reports before finishing. Root: LEAN_PROJECT_ROOT, else the opened file's project, else the current directory."
  inputSchema := Json.mkObj [("type", "object"), ("properties", Json.mkObj [])]
  handler := verifyToolHandler ref
}

/-! ### tool registry -/

/-- Order matches the Python original's `ALL_TOOLS`. -/
def allTools (ref : IO.Ref (Option Driver.Session)) : List Mcp.Tool :=
  [openTool ref, buildTool, verifyTool ref, stepTool ref, rollbackTool ref, stateTool ref,
   tryTool ref, autoCloseTool ref, checkTool ref]

def defaultEnabled : List String :=
  ["open", "build", "verify", "check", "step", "rollback", "state", "try", "auto_close"]

end LeanMcpEvolve.Session
