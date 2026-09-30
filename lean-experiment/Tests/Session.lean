/-
Tests.Session — suite A: session-server core contracts, ported case-for-case
from `prototype-python/tests/test_session.py` (see
`prototype-python/tests/ARCHITECTURE.md`'s "suite A" section for the
one-line description of each case this file cites in its own comments).
Every case spawns a FRESH server (sessions are single-task) against the
core-only test project (`Tests.Helpers.coreProject`, no Mathlib), drives it
over MCP stdio, asserts on the SAME response substrings as the Python
original, and closes it.

Each case is wrapped in `runCase`, which catches any uncaught exception
(e.g. "server closed stdout" if the binary under test crashes or hasn't been
built yet) and turns it into a single FAIL rather than aborting the whole
suite — later cases still get a chance to run, and the planner still gets a
diagnosable line.
-/
import Tests.Helpers

namespace Tests.Session

open Lean (Json)
open Tests.Helpers (Server Stats check contains startsWith coreProject fixture writeFile readFile tmpdir freshSuffix spawnServer repoRoot getFloatField)

def candidatePath (wd : System.FilePath) : System.FilePath := wd / "candidate.lean"

/-- Absolute path to the built `gate` executable (same convention as
`Tests.Gate.gateBinPath`). -/
def gateBinPath : IO System.FilePath := do
  pure ((← repoRoot) / ".lake" / "build" / "bin" / "gate")

structure GateCliResult where
  exitCode : UInt32
  stdout   : String

/-- Run the `gate` executable as a subprocess, `lake env`-wrapped from `proj`
(the core project directory, so its own `LEAN_PATH` resolves) -- the harness
step a benchmark runs AFTER the in-session server has already reported
PROOF COMPLETE and written `cand`, exactly as rocq-mcp-evolve's harness runs
`harness/gate.py` after the Rocq server accepts `Admitted.`. Mirrors
`Tests.Gate.runGateCli`. `reference?`, when given, is passed as `--reference`
(the harness's real invocation): now that `Driver.candidateText` no longer
inserts a stray separator newline before its captured file tail (see A29),
this is byte-exact against the original task file outside the target's own
proof, so a `--reference` run of a genuine proof is ACCEPTED. A21/A22/A24
below still omit it since those cases test the forbidden-token/axiom-audit
rejection layers, which don't need the reference check at all. -/
def runGateCli (proj cand : System.FilePath) (theoremName : String) (reference? : Option System.FilePath := none) :
    IO GateCliResult := do
  let bin ← gateBinPath
  let refArgs := match reference? with
    | some r => #["--reference", r.toString]
    | none => #[]
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", bin.toString, cand.toString, "--theorem", theoremName, "--project", proj.toString] ++ refArgs
    cwd := some proj }
  pure { exitCode := out.exitCode, stdout := out.stdout }

/-- Write a fixture (or literal `content`) into the core project under a
fresh, unique name, and return `(workdir, taskfile)` — port of Python's
`setup_task`. -/
def setupTask (name : String) (content? : Option String := none) : IO (System.FilePath × System.FilePath) := do
  let proj ← coreProject
  let wd ← tmpdir "sessA_"
  let n ← freshSuffix
  let task := proj / "Coreproj" / s!"T{n}.lean"
  let content ← match content? with
    | some c => pure c
    | none => fixture name
  writeFile task content
  pure (wd, task)

/-- Port of Python's `base_env`. -/
def baseEnv (workdir taskfile : System.FilePath) (tools : String := "") (extra : List (String × String) := []) :
    List (String × String) :=
  let base := [("LEAN_ENV_V2", "1"), ("LEAN_TASK_FILE", taskfile.toString), ("LEAN_WORKDIR", workdir.toString)]
  let withTools := if tools.isEmpty then base else base ++ [("LEAN_ENABLE_TOOLS", tools)]
  withTools ++ extra

/-- Spawn against the core project with `LEAN_TASK_FILE`/`LEAN_WORKDIR`
preset (the common case: every fixture-based test), and `initialize`. -/
def spawn (wd tf : System.FilePath) (tools : String := "") (extra : List (String × String) := []) : IO Server := do
  let proj ← coreProject
  let s ← spawnServer proj (baseEnv wd tf tools extra)
  let _ ← s.initialize
  pure s

/-- Spawn with a fully custom `env` (the "runtime open" tests, A12/A14/A15,
which do not preset `LEAN_TASK_FILE`), and `initialize`. -/
def spawnEnv (cwd : System.FilePath) (env : List (String × String)) : IO Server := do
  let s ← spawnServer cwd env
  let _ ← s.initialize
  pure s

def withServer (wd tf : System.FilePath) (tools : String := "") (extra : List (String × String) := [])
    (body : Server → IO Unit) : IO Unit := do
  let s ← spawn wd tf tools extra
  try body s finally s.close

def withServerEnv (cwd : System.FilePath) (env : List (String × String)) (body : Server → IO Unit) : IO Unit := do
  let s ← spawnEnv cwd env
  try body s finally s.close

/-- Run one test case, catching any uncaught exception (e.g. the server
binary not existing yet, or crashing) as a single FAIL rather than aborting
the rest of the suite. -/
def runCase (statsRef : IO.Ref Stats) (name : String) (action : IO.Ref Stats → IO Unit) : IO Unit := do
  try
    action statsRef
  catch e =>
    check statsRef false s!"{name} (uncaught exception)" s!"{e}"

-- A0 — the surface is exactly rocq-mcp-evolve's nine tools; LEAN_ENABLE_TOOLS trims
def a0 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  let expected := ["open", "build", "verify", "check", "step", "try", "auto_close", "rollback", "state"]
  withServer wd tf "" [] fun s => do
    let tools ← s.tools
    check statsRef (tools.length == expected.length && expected.all tools.contains)
      "A0 tool surface (full, unordered set)" s!"{tools}"
  withServer wd tf "step,state" [] fun s2 => do
    let tools2 ← s2.tools
    check statsRef (tools2.length == 2 && tools2.contains "step" && tools2.contains "state")
      "A0 tool surface (LEAN_ENABLE_TOOLS=step,state)" s!"{tools2}"

-- A1 commit-good-prefix (Rocq A1): LEAN_TASK_FILE preset opens the session lazily
def a1 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  withServer wd tf "step" [] fun s => do
    let r1 ← s.call "step" (Json.mkObj [("text", "show n + 0 + 0 = n\nbogus_tac")])
    check statsRef (contains r1 "1 tactic(s) committed") "A1 1 tactic committed" r1
    check statsRef (contains r1 "ERROR at `bogus_tac`") "A1 ERROR at bogus_tac" r1
    let r2 ← s.call "step" (Json.mkObj [("text", "induction n with\n| zero => rfl\n| succ n ih => rfl")])
    check statsRef (contains r2 "PROOF COMPLETE") "A1 PROOF COMPLETE" r2
    let exists_ ← (candidatePath wd).pathExists
    check statsRef exists_ "A1 candidate.lean exists"
    if exists_ then
      let content ← readFile (candidatePath wd)
      check statsRef (((content.splitOn "show n + 0 + 0 = n").length - 1) == 1)
        "A1 candidate has prefix exactly once (no duplication)" content
      check statsRef (!contains content "sorry") "A1 candidate has no sorry" content

-- A2 auto-Qed handshake: no explicit closer needed (atlas fix 1 / A25)
def a2 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  withServer wd tf "step" [] fun s => do
    let r ← s.call "step" (Json.mkObj [("text", "simp")])
    check statsRef (contains r "PROOF COMPLETE") "A2 PROOF COMPLETE" r
    check statsRef (contains r "theorem t2") "A2 finished declaration echoed" r
    let content ← readFile (candidatePath wd)
    check statsRef (content.trimAsciiEnd.toString.endsWith "simp") "A2 candidate ends with simp" content

-- A3 try semantics: independent evaluation, first full success commits
def a3 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F3.lean"
  withServer wd tf "try,state" [] fun s => do
    let cands := Json.arr (#["bogus", "constructor\nexact hp", "constructor\nexact hp\nexact hq", "exact ⟨hp, hq⟩"].map Json.str)
    let r ← s.call "try" (Json.mkObj [("candidates", cands)])
    check statsRef (contains r "[1] `bogus` — syntax error") "A3 [1] syntax error" r
    check statsRef (contains r "[2] `constructor ⏎ exact hp` — OK, 1 goal(s) left; next: q  << COMMITTED")
      "A3 [2] committed even with goals left (Rocq: Full)" r
    check statsRef (contains r "[3] `constructor ⏎ exact hp ⏎ exact hq` — OK, closes ALL goals  (not committed)")
      "A3 [3] full closer not committed (came after [2])" r
    check statsRef (contains r "[4] `exact ⟨hp, hq⟩` — OK, closes ALL goals  (not committed)")
      "A3 [4] full closer not committed" r
    check statsRef (contains r "after commit:\ngoals: 1") "A3 after commit goals: 1" r
    let exists1 ← (candidatePath wd).pathExists
    check statsRef (!exists1) "A3 no candidate.lean (goal still open)"
    let cands2 := Json.arr (#["exact hp", "exact hq"].map Json.str)
    let r2 ← s.call "try" (Json.mkObj [("candidates", cands2)])
    check statsRef (contains r2 "[2] `exact hq` — OK, closes ALL goals  << COMMITTED") "A3 second try commits" r2
    check statsRef (contains r2 "PROOF COMPLETE") "A3 second try completes" r2
    let content ← readFile (candidatePath wd)
    check statsRef (contains content "exact hp\n") "A3 candidate contains committed exact hp" content

-- A3b try with commit:none leaves the state untouched, each candidate evaluated
-- from the same state (a closer does not poison later ones)
def a3b (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  withServer wd tf "try,state" [] fun s => do
    let cands := Json.arr (#["simp", "omega", "rfl"].map Json.str)
    let r ← s.call "try" (Json.mkObj [("candidates", cands), ("commit", "none")])
    let okCount := (r.splitOn "OK, closes ALL goals").length - 1
    check statsRef (okCount == 3) "A3b all three candidates report OK, closes ALL goals" r
    check statsRef (contains r "nothing committed; state unchanged") "A3b nothing committed" r
    let st ← s.call "state"
    check statsRef (contains st "(nothing committed yet)") "A3b state still nothing committed" st
    let exists_ ← (candidatePath wd).pathExists
    check statsRef (!exists_) "A3b no candidate.lean"

-- A4 auto_close progress rule (A22 false-winner regression): a no-op tactic
-- must not count as a win; on F3 nothing closes ∧ without structural work
def a4 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F3.lean"
  withServer wd tf "auto_close" [("LEAN_AUTO_SEARCH", "0")] fun s => do
    let r ← s.call "auto_close"
    if contains r "no finisher applies" then
      let exists_ ← (candidatePath wd).pathExists
      check statsRef (!exists_) "A4 honest miss: no candidate.lean" r
    else
      check statsRef (contains r "COMMITTED") "A4 real closure: COMMITTED" r
      check statsRef (contains r "PROOF COMPLETE") "A4 real closure: PROOF COMPLETE" r
      let exists_ ← (candidatePath wd).pathExists
      check statsRef exists_ "A4 real closure: candidate.lean exists" r

-- A4b auto_close closes an arithmetic goal with a core finisher
def a4b (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  withServer wd tf "auto_close" [("LEAN_AUTO_SEARCH", "0")] fun s => do
    let r ← s.call "auto_close"
    check statsRef (contains r "COMMITTED") "A4b COMMITTED" r
    check statsRef (contains r "PROOF COMPLETE") "A4b PROOF COMPLETE" r
    let exists_ ← (candidatePath wd).pathExists
    check statsRef exists_ "A4b candidate.lean exists"

-- A6 rollback + query non-commit (Rocq A6)
def a6 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F3.lean"
  withServer wd tf "step,rollback,state" [] fun s => do
    let r ← s.call "step" (Json.mkObj [("text", "constructor\n#check And.intro")])
    check statsRef (contains r "And.intro") "A6 #check output shown" r
    check statsRef (contains r "1 tactic(s) committed (1 query command(s) executed, not committed)")
      "A6 query executed but not committed" r
    check statsRef (contains r "goals: 2") "A6 goals: 2" r
    let r2 ← s.call "rollback" (Json.mkObj [("count", 1)])
    check statsRef (contains r2 "rolled back 1") "A6 rolled back 1" r2
    check statsRef (contains r2 "goals: 1") "A6 goals: 1 after rollback" r2
    let st ← s.call "state"
    check statsRef (contains st "(nothing committed yet)") "A6 state nothing committed after rollback" st
    let r3 ← s.call "step" (Json.mkObj [("text", "exact ⟨hp, hq⟩")])
    check statsRef (contains r3 "PROOF COMPLETE") "A6 PROOF COMPLETE" r3
    let content ← readFile (candidatePath wd)
    check statsRef (!contains content "#check") "A6 candidate never contains #check" content

-- A7 refusal parity with rocq-mcp-evolve's `reject_require`: under
-- LEAN_ENV_V2=1 the ONLY refusal THAT IS GATED BY IT is `import` (the Lean
-- analogue of `Require`, since Lean cannot import mid-file either).
--
-- `sorry` is a SEPARATE, UNCONDITIONAL refusal (`Session.firstSorryUnit`,
-- restored 2026-09-08): a `sorry` unit is refused up front, reported as a
-- tactic ERROR, and never executed/committed -- it does NOT complete the
-- proof, in ANY mode. This corrects a false parity claim: the earlier design
-- had `sorry` EXECUTE and, once it closed the goal, reported PROOF COMPLETE,
-- on the theory that this matched rocq-mcp-evolve's own session server
-- accepting `Admitted.` -- but the Rocq server's completion signal is "a
-- `Qed.` was submitted and succeeded", and `Qed.` FAILS after `admit`;
-- `Admitted.` is a distinct command the tactic-running tools never submit.
-- There was never a "placeholder completes" case on the Rocq side to match.
--
-- The refusal is decided on the unit's own PARSED syntax, so a `sorry`
-- hidden in a comment or inside a string literal never triggers it (neither
-- ever makes it into `Syntax`) -- see A21/A22/A24/A25/A27/A28 for how a
-- completion that depends on a disallowed axiom (no literal `sorry` token
-- involved at all) is now ALSO refused, by `Driver.completionCheck`'s axiom
-- audit.
def a7 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  let logf := wd / "log.jsonl"
  withServer wd tf "step,state" [("LEAN_LOG_FILE", logf.toString)] fun s => do
    let r ← s.call "step" (Json.mkObj [("text", "import Mathlib")])
    check statsRef (contains r "`import` is not allowed") "A7 import refused with the new message" r
    check statsRef (contains r "imports are fixed") "A7 message explains fixed imports" r
    let st ← s.call "state"
    check statsRef (contains st "(nothing committed yet)") "A7 nothing committed after refused import" st
    let exists0 ← (candidatePath wd).pathExists
    check statsRef (!exists0) "A7 no candidate.lean after refused import"
    -- a bare `sorry` unit: refused, reported like a failed tactic, nothing
    -- committed, state unchanged, no candidate written.
    let r2 ← s.call "step" (Json.mkObj [("text", "sorry")])
    check statsRef (contains r2 "0 tactic(s) committed, then ERROR at `sorry`:")
      "A7 sorry reported as an ERROR, nothing committed for it" r2
    check statsRef (contains r2 "`sorry` is not allowed") "A7 sorry error message" r2
    check statsRef (contains r2 "state unchanged since last success") "A7 sorry error uses the standard error shape" r2
    check statsRef (!contains r2 "PROOF COMPLETE") "A7 sorry does NOT complete" r2
    let st2 ← s.call "state"
    check statsRef (contains st2 "(nothing committed yet)") "A7 still nothing committed after refused sorry" st2
    let exists1 ← (candidatePath wd).pathExists
    check statsRef (!exists1) "A7 no candidate.lean after refused sorry"
    -- a `sorry` inside a `--` comment, and inside a string literal, are NOT
    -- refused (neither is ever parsed `Syntax`) -- the unit still executes.
    let r3 ← s.call "step" (Json.mkObj [("text", "-- sorry\nhave h := \"sorry\"")])
    check statsRef (!contains r3 "not allowed") "A7 a commented-out/string-literal sorry is NOT refused" r3
    check statsRef (contains r3 "1 tactic(s) committed") "A7 the have-with-string-literal tactic executed" r3
    let content ← readFile logf
    let lines := (content.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
    let recs := lines.filterMap (fun l => (Json.parse l).toOption)
    let sorryRejectedRecs := recs.filter (fun r =>
      r.getObjValD "kind" == Json.str "tool_call" && r.getObjValD "stop" == Json.str "sorry_rejected")
    check statsRef (sorryRejectedRecs.length == 1) "A7 exactly one tool_call logged stop:sorry_rejected" s!"{recs}"

-- A7b a nested `sorry` (`have h : P := by sorry`, not the bare keyword on
-- its own line) inside a longer multi-line unit is refused with the SAME
-- commit-good-prefix semantics: earlier tactics in the call stay committed,
-- the sorry-carrying unit is reported as the error, later tactics in the
-- call never run.
def a7b (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  withServer wd tf "step,state" [] fun s => do
    let r ← s.call "step"
      (Json.mkObj [("text", "show n + 0 + 0 = n\nhave h : n = n := by sorry\nrfl")])
    check statsRef (contains r "1 tactic(s) committed, then ERROR at `have h : n = n := by sorry`:")
      "A7b earlier tactic committed, nested sorry unit reported as the error" r
    check statsRef (contains r "`sorry` is not allowed") "A7b nested sorry error message" r
    check statsRef (!contains r "PROOF COMPLETE") "A7b does not complete" r
    let st ← s.call "state"
    check statsRef (contains st "show n + 0 + 0 = n") "A7b the earlier tactic stayed committed" st
    let exists_ ← (candidatePath wd).pathExists
    check statsRef (!exists_) "A7b no candidate.lean written"

-- A8 error enrichment: Rocq-isms rewritten, near-miss names appended
def a8 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  withServer wd tf "step" [("LEAN_HINTS", "1"), ("LEAN_SUGGEST", "1")] fun s => do
    let r ← s.call "step" (Json.mkObj [("text", "intros n.")])
    check statsRef (contains r "hint:") "A8 hint: present (intros n.)" r
    check statsRef (contains r "period" || contains r "Rocq") "A8 hint mentions period/Rocq" r
    let r2 ← s.call "step" (Json.mkObj [("text", "rewrite Nat.add_zero")])
    check statsRef (contains r2 "hint:") "A8 hint: present (rewrite)" r2
    check statsRef (contains r2 "rw [h]") "A8 hint suggests rw [h]" r2
    let r3 ← s.call "step" (Json.mkObj [("text", "exact Nat.add_zerro n")])
    check statsRef (contains r3 "near-miss") "A8 near-miss present" r3
    check statsRef (contains r3 "Nat.add_zero") "A8 near-miss names Nat.add_zero" r3
    let r4 ← s.call "step" (Json.mkObj [("text", "rollback")])
    check statsRef (contains r4 "is a TOOL") "A8 tool-name-as-tactic caught" r4

-- A9 check tool: fresh-attempt semantics + repair-from-failure
def a9 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F3.lean"
  withServer wd tf "check,step,state" [] fun s => do
    let r ← s.call "check" (Json.mkObj [("script", "by\n  constructor\n  exact hq\n  exact hq")])
    check statsRef (contains r "1 tactic(s) committed, then ERROR at `exact hq`") "A9 error at exact hq" r
    check statsRef (contains r "you are now AT that point") "A9 repair phrasing" r
    check statsRef (contains r "goals: 2") "A9 goals: 2" r
    let r2 ← s.call "check" (Json.mkObj [("script", "constructor\nexact hp\nexact hq")])
    check statsRef (contains r2 "(fresh attempt: 1 previously committed tactic(s) discarded)") "A9 fresh attempt discards prior work" r2
    check statsRef (contains r2 "PROOF COMPLETE") "A9 fresh attempt completes" r2

-- A12 runtime open (A29): pre-open tools direct to open; relative paths;
-- first-unproven default; named theorem; missing file/theorem errors; the
-- candidate is the whole file with only the target proof replaced
def a12 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "sessA_"
  withServerEnv proj [("LEAN_WORKDIR", wd.toString)] fun s => do
    let r1 ← s.call "step" (Json.mkObj [("text", "simp")])
    check statsRef (contains r1 "call the `open` tool") "A12 pre-open guard directs to open" r1
    let r2 ← s.call "open" (Json.mkObj [("file", "/nonexistent/X.lean")])
    check statsRef (contains r2 "no such file") "A12 no such file" r2
    let f := proj / "Coreproj" / "Multi.lean"
    writeFile f
      ("theorem m1 (n : Nat) : n = n := by\n  rfl\n\n" ++
       "theorem m2 (n : Nat) : n + 0 = n := by\n  sorry\n\n" ++
       "theorem m3 : 1 + 1 = 2 := by\n  sorry\n")
    let r3 ← s.call "open" (Json.mkObj [("file", "Coreproj/Multi.lean")])
    check statsRef (contains r3 "proving m2") "A12 first-unproven default (m2)" r3
    check statsRef (contains r3 "⊢ n + 0 = n") "A12 m2 goal shown" r3
    let r4 ← s.call "open" (Json.mkObj [("file", f.toString), ("theorem", "m3")])
    check statsRef (contains r4 "proving m3") "A12 named theorem (m3)" r4
    check statsRef (contains r4 "⊢ 1 + 1 = 2") "A12 m3 goal shown" r4
    let r5 ← s.call "open" (Json.mkObj [("file", f.toString), ("theorem", "nope")])
    check statsRef (contains r5 "not found") "A12 missing theorem error" r5
    let r6 ← s.call "step" (Json.mkObj [("text", "rfl")])
    check statsRef (contains r6 "PROOF COMPLETE") "A12 m3 provable via rfl" r6
    let c ← readFile (candidatePath wd)
    check statsRef (contains c "theorem m2 (n : Nat) : n + 0 = n := by\n  sorry") "A12 candidate: m2 untouched" c
    check statsRef (contains c "theorem m3 : 1 + 1 = 2 := by\n  rfl") "A12 candidate: m3 replaced" c

-- A14 build: whole-file multi-error diagnosis, holes reachable by open
-- (A36: a theorem after a broken proof must be provable)
def a14 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "sessA_"
  let f := proj / "Coreproj" / "BuildFx.lean"
  let buildFixture ← fixture "Build.lean"
  writeFile f buildFixture
  withServerEnv proj [("LEAN_WORKDIR", wd.toString)] fun s => do
    let r ← s.call "build" (Json.mkObj [("file", f.toString)])
    check statsRef (contains r "BUILD: 2 declaration(s) OK, 3 hole(s)") "A14 build summary (2 OK, 3 holes)" r
    check statsRef (contains r "- b1:") "A14 b1 listed" r
    check statsRef (contains r "- b2: uses `sorry`") "A14 b2 uses sorry" r
    check statsRef (contains r "- b5:") "A14 b5 listed" r
    check statsRef (contains r "is false") "A14 b5 is a false decide" r
    let r2 ← s.call "open" (Json.mkObj [("file", f.toString), ("theorem", "b4")])
    check statsRef (contains r2 "proving b4") "A14 open b4 (past the broken b1)" r2
    check statsRef (contains r2 "earlier declarations") "A14 note about earlier declarations" r2
    let r3 ← s.call "step" (Json.mkObj [("text", "omega")])
    check statsRef (contains r3 "PROOF COMPLETE") "A14 b4 provable via omega" r3
    let st ← s.call "state"
    check statsRef (contains st "PROOF COMPLETE") "A14 build is pure: session still on b4, complete" st
    let r4 ← s.call "build" (Json.mkObj [("file", f.toString)])
    check statsRef (contains r4 "3 hole(s)") "A14 build unaffected by the session" r4

-- A15 verify: forbidden-token scan + lake build
def a15 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "sessA_"
  withServerEnv proj [("LEAN_WORKDIR", wd.toString), ("LEAN_PROJECT_ROOT", proj.toString)] fun s => do
    let r ← s.call "verify"
    check statsRef (startsWith r "VERIFY OK" || contains r "forbidden token `sorry`")
      "A15 verify: clean, or lists forbidden sorry from other tests' fixtures" r

-- A16 timeout safety: a slow tactic is cancelled and reported structurally,
-- the session keeps working afterwards
def a16 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "Slow.lean" (some "theorem slow : ∀ a b c : Fin 40, a + b + c = c + b + a := by\n  sorry\n")
  withServer wd tf "step,state" [("LEAN_STEP_TIMEOUT", "2")] fun s => do
    let r ← s.call "step" (Json.mkObj [("text", "decide")])
    check statsRef (contains r "TIMEOUT" || contains r "heartbeats") "A16 TIMEOUT or heartbeats error" r
    check statsRef (contains r "0 tactic(s) committed") "A16 nothing committed" r
    let r2 ← s.call "step" (Json.mkObj [("text", "intro a b c\nomega")])
    check statsRef (contains r2 "PROOF COMPLETE") "A16 session still usable after timeout" r2

-- A17 search tactics are committed as what they find
def a17 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  withServer wd tf "step,state" [] fun s => do
    let r ← s.call "step" (Json.mkObj [("text", "exact?")])
    check statsRef (contains r "PROOF COMPLETE") "A17 PROOF COMPLETE" r
    let c ← readFile (candidatePath wd)
    check statsRef (!contains c "exact?") "A17 candidate is the found tactic, not exact?" c
    check statsRef (contains r "found:") "A17 response reports found:" r

-- A18 already-complete guard on every mutating tool; rollback reopens
def a18 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  withServer wd tf "step,state,try,auto_close,check,rollback" [] fun s => do
    let _ ← s.call "step" (Json.mkObj [("text", "omega")])
    let r1 ← s.call "step" (Json.mkObj [("text", "simp")])
    check statsRef (contains r1 "already COMPLETE") "A18 step guard" r1
    let r2 ← s.call "try" (Json.mkObj [("candidates", Json.arr #[Json.str "simp"])])
    check statsRef (contains r2 "already COMPLETE") "A18 try guard" r2
    let r3 ← s.call "auto_close"
    check statsRef (contains r3 "already COMPLETE") "A18 auto_close guard" r3
    let r4 ← s.call "check" (Json.mkObj [("script", "simp")])
    check statsRef (contains r4 "already COMPLETE") "A18 check guard" r4
    let st ← s.call "state"
    check statsRef (contains st "PROOF COMPLETE") "A18 state shows complete" st
    let r5 ← s.call "rollback" (Json.mkObj [("count", 1)])
    check statsRef (contains r5 "rolled back 1") "A18 rollback still works when complete" r5
    check statsRef (contains r5 "goals: 1") "A18 rollback reopens the goal" r5

-- A19 multi-line units (induction alternatives, bullets) are one tactic each
def a19 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F3.lean"
  withServer wd tf "step,state" [] fun s => do
    let r ← s.call "step" (Json.mkObj [("text", "constructor\n· exact hp\n· exact hq")])
    check statsRef (contains r "3 tactic(s) committed") "A19 3 tactics committed (constructor + 2 bullets)" r
    check statsRef (contains r "PROOF COMPLETE") "A19 PROOF COMPLETE" r
    check statsRef (contains r "· exact hp") "A19 bullet text preserved" r

-- A20 instrumentation: one JSONL record per tool call, merged with LEAN_LOG_META
def a20 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  let logf := wd / "log.jsonl"
  withServer wd tf "step" [("LEAN_LOG_FILE", logf.toString), ("LEAN_LOG_META", "{\"run\": \"r1\"}")] fun s => do
    let _ ← s.call "step" (Json.mkObj [("text", "omega")])
    let content ← readFile logf
    let lines := (content.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
    let recs := lines.filterMap (fun l => (Json.parse l).toOption)
    let kinds := recs.map (fun r => match r.getObjValD "kind" with | .str k => k | _ => "")
    check statsRef (kinds.contains "initialize") "A20 initialize record present" s!"{kinds}"
    check statsRef (kinds.contains "tool_call") "A20 tool_call record present" s!"{kinds}"
    match recs.find? (fun r => r.getObjValD "kind" == Json.str "tool_call") with
    | none => check statsRef false "A20 tool_call record found (for field checks)"
    | some tc =>
      check statsRef (tc.getObjValD "tool" == Json.str "step") "A20 tool field == step" s!"{tc}"
      check statsRef (tc.getObjValD "run" == Json.str "r1") "A20 LEAN_LOG_META merged (run == r1)" s!"{tc}"
      check statsRef (tc.getObjValD "complete" == Json.bool true) "A20 complete field true" s!"{tc}"

-- A21 axiom injection in-session: `run_tac` itself is refused in NO mode
-- (refusal parity with rocq-mcp-evolve's `reject_require`, which refuses
-- only `import`/`Require`, see A7 -- and it contains no `sorry`/`sorryAx`/
-- `admit` token either, so `firstSorryUnit` never touches it), so the
-- injection step always runs and the goal-closing `exact cheat.elim` step
-- runs too (no literal `sorry` anywhere for the up-front refusal to catch).
-- But `Driver.completionCheck` now audits `Lean.collectAxioms` of the
-- re-elaborated target (README "Verification" §1, restored 2026-09-08): the
-- injected `cheat` axiom is not in `standardAxioms`, so completion is
-- refused IN-SESSION -- no `PROOF COMPLETE`, no `candidate.lean` written,
-- nothing left for the out-of-process gate to even be handed. Run both with
-- and without `LEAN_ENV_V2` to confirm this refusal does not depend on it.
def axiomInjectStep : String :=
  "run_tac do Lean.addDecl (Lean.Declaration.axiomDecl " ++
    "{ name := `cheat, levelParams := [], type := Lean.mkConst ``False, isUnsafe := false })"

def a21Body (label : String) (statsRef : IO.Ref Stats) (_proj wd : System.FilePath) (s : Server) : IO Unit := do
  let r1 ← s.call "step" (Json.mkObj [("text", axiomInjectStep)])
  check statsRef (!contains r1 "PROOF COMPLETE") s!"{label} axiom-injection step itself never completes" r1
  let r2 ← s.call "step" (Json.mkObj [("text", "exact cheat.elim")])
  check statsRef (!contains r2 "PROOF COMPLETE")
    s!"{label} exact cheat.elim does NOT complete in-session (disallowed axiom `cheat`)" r2
  let st ← s.call "state"
  check statsRef (!contains st "PROOF COMPLETE") s!"{label} state NOT complete" st
  let exists_ ← (candidatePath wd).pathExists
  check statsRef (!exists_) s!"{label} no candidate.lean written (never completed)"

/-- `run_tac`'s injected `do`-block needs `TacticM`/`Lean.mkConst`/
`Lean.Declaration` in scope, so (unlike every other fixture in this suite)
this task file needs `import Lean` -- without it `run_tac` itself fails to
elaborate (`Unknown constant Lean.Elab.Tactic.TacticM`) before ever reaching
the axiom. -/
def a21TaskFile : String :=
  "import Lean\n\ntheorem t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n"

def a21 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let (wd1, tf1) ← setupTask "T21.lean" (some a21TaskFile)
  withServer wd1 tf1 "step,state" [] fun s => a21Body "A21 (LEAN_ENV_V2=1)" statsRef proj wd1 s
  let (wd2, tf2) ← setupTask "T21.lean" (some a21TaskFile)
  withServerEnv proj
    [("LEAN_TASK_FILE", tf2.toString), ("LEAN_WORKDIR", wd2.toString), ("LEAN_ENABLE_TOOLS", "step,state")]
    fun s => a21Body "A21 (no LEAN_ENV_V2)" statsRef proj wd2 s

-- A22 `native_decide` still EXECUTES (it is not refused up front -- no
-- `sorry`/`sorryAx`/`admit` token, and refusal parity only ever gated
-- `import`): it closes the goal and elaborates without error, so `step`'s
-- own tactic-execution check passes. But it depends on the
-- `Lean.ofReduceBool` axiom, which is not in `standardAxioms`, so
-- `Driver.completionCheck`'s axiom audit now refuses completion IN-SESSION
-- (restored 2026-09-08) -- no `PROOF COMPLETE`, no `candidate.lean` written.
def a22 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "T22.lean" (some "theorem t : (2 : Nat) + 2 = 4 := by\n  sorry\n")
  withServer wd tf "step,state" [] fun s => do
    let r ← s.call "step" (Json.mkObj [("text", "native_decide")])
    check statsRef (!contains r "not allowed") "A22 native_decide is NOT refused up front (executes)" r
    check statsRef (!contains r "PROOF COMPLETE")
      "A22 native_decide does NOT complete in-session (disallowed axiom Lean.ofReduceBool)" r
    let st ← s.call "state"
    check statsRef (!contains st "PROOF COMPLETE") "A22 state NOT complete" st
    let exists_ ← (candidatePath wd).pathExists
    check statsRef (!exists_) "A22 no candidate.lean written (never completed)"

-- A23 `example` completion: the target constant elaborates anonymously (no
-- name to relocate in the environment), so `Driver.completionCheck` must
-- audit it under a synthetic `theorem` name instead of best-effort-passing
-- when the lookup comes back empty (the old, unsafe fallback).
def a23 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "T23.lean" (some "example (n : Nat) : n + 0 = n := by\n  sorry\n")
  withServer wd tf "step,state" [] fun s => do
    let r ← s.call "step" (Json.mkObj [("text", "simp")])
    check statsRef (contains r "PROOF COMPLETE") "A23 PROOF COMPLETE" r
    let content ← readFile (candidatePath wd)
    check statsRef (contains content "example (n : Nat) : n + 0 = n := by\n  simp")
      "A23 candidate holds the example, proof replaced by simp" content

-- A24 `sorryAx` spelled directly (bypassing the plain `sorry` keyword):
-- caught by the SAME up-front refusal as a bare `sorry` -- `Text.sorryHit`
-- walks the unit's parsed syntax for `sorryAx` as an IDENTIFIER, not just
-- `sorry` as an atom, so `exact (sorryAx _ false)` never even executes.
-- Nothing is committed, and no `candidate.lean` is ever written.
def a24 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  withServer wd tf "step,state" [] fun s => do
    let r ← s.call "step" (Json.mkObj [("text", "exact (sorryAx _ false)")])
    check statsRef (contains r "0 tactic(s) committed, then ERROR at `exact (sorryAx _ false)`:")
      "A24 sorryAx refused up front, nothing committed" r
    check statsRef (contains r "`sorryAx` is not allowed") "A24 sorryAx error message" r
    check statsRef (!contains r "PROOF COMPLETE") "A24 sorryAx does NOT complete" r
    let st ← s.call "state"
    check statsRef (contains st "(nothing committed yet)") "A24 nothing committed" st
    let exists_ ← (candidatePath wd).pathExists
    check statsRef (!exists_) "A24 no candidate.lean written"

-- A25 `try` reports a `sorry` candidate as an ERROR (never speculated,
-- never committed -- `firstSorryUnit` rejects the whole candidate up front,
-- same message as `step`/`check`); the next candidate that fully succeeds
-- (`omega`) is committed instead, exactly as if the `sorry` candidate had
-- simply failed.
def a25 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  withServer wd tf "try,state" [] fun s => do
    let cands := Json.arr (#["sorry", "omega"].map Json.str)
    let r ← s.call "try" (Json.mkObj [("candidates", cands)])
    check statsRef (contains r "[1] `sorry` — error at `sorry`:") "A25 sorry candidate reported as an error" r
    check statsRef (contains r "`sorry` is not allowed") "A25 sorry candidate error message" r
    check statsRef (contains r "[2] `omega` — OK, closes ALL goals  << COMMITTED")
      "A25 omega COMMITTED instead (sorry candidate never touched the state)" r
    check statsRef (contains r "PROOF COMPLETE") "A25 PROOF COMPLETE via omega" r
    let exists_ ← (candidatePath wd).pathExists
    check statsRef exists_ "A25 candidate.lean exists"
    if exists_ then
      let content ← readFile (candidatePath wd)
      check statsRef (!contains content "sorry") "A25 candidate does not contain sorry" content

-- A27 the opt-in `LEAN_GATE=1` hook still has genuine value beyond the
-- in-session refusal/audit (NOT part of the Rocq protocol itself -- see
-- README's Verification section): `sorry` is refused before it can ever
-- complete now (A7), and a disallowed-axiom completion is refused
-- in-session too (A21/A22), so this case is rewritten around what the gate
-- ALONE can still catch -- an "unchecked smuggle" that fools the
-- SAME-PROCESS checks (`run_tac`, from a tactic, locally overrides
-- `debug.skipKernelTC` back to `true` around a single `Lean.addDecl` call,
-- so an ill-typed "theorem" is added WITHOUT the kernel ever checking it;
-- `completionCheck`'s re-elaboration re-runs the very same script and is
-- fooled the very same way, and the smuggled constant is a THEOREM, not an
-- `axiomDecl`, so `Lean.collectAxioms` never sees it either). The
-- standalone gate catches it two ways: its own earlier forbidden-token
-- scan already forbids `run_tac` on the parsed `Syntax` (same reason
-- `Tests.Gate`'s D7 asserts on its ordinary CLI run), and even a candidate
-- that dodged THAT check would still be caught one step later by kernel
-- REPLAY of every locally-added constant into a FRESH environment (D7's
-- token-check-BYPASSED variant proves step 6 alone rejects this ill-typed
-- `cheat`). Either way, this is something only a fresh, independent process
-- can catch -- `completionCheck`'s in-session re-elaboration re-runs the
-- very same script in the very same process and is fooled the very same
-- way. With `LEAN_GATE=1`, the session hands every completion to that same
-- gate before ever telling the agent PROOF COMPLETE, so this candidate is
-- rejected right there, with the last committed unit rolled back and
-- `candidate.lean` removed again.
def a27InjectStep : String :=
  "run_tac do\n" ++
  "    Lean.withOptions (fun o => Lean.debug.skipKernelTC.set o true) do\n" ++
  "      Lean.addDecl (Lean.Declaration.thmDecl\n" ++
  "        { name := `cheat, levelParams := [], type := Lean.mkConst ``False, value := Lean.mkConst ``True.intro })"

def a27 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "sessA_"
  let n ← freshSuffix
  let f := proj / "Coreproj" / s!"T27_{n}.lean"
  writeFile f "import Lean\n\ntheorem t27 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n"
  let gateBin ← gateBinPath
  withServerEnv proj [("LEAN_WORKDIR", wd.toString), ("LEAN_GATE", "1"), ("LEAN_GATE_BIN", gateBin.toString)]
      fun s => do
    let _ ← s.call "open" (Json.mkObj [("file", f.toString)])
    let r1 ← s.call "step" (Json.mkObj [("text", a27InjectStep)])
    check statsRef (!contains r1 "PROOF COMPLETE") "A27 the smuggle step itself never completes" r1
    let r2 ← s.call "step" (Json.mkObj [("text", "exact cheat.elim")])
    check statsRef (contains r2 "candidate REJECTED by the gate")
      "A27 LEAN_GATE=1 rejects the unchecked-smuggle candidate before PROOF COMPLETE" r2
    check statsRef (contains r2 "forbidden_token:run_tac")
      "A27 gate reason: run_tac forbidden at its own token check (D7's kernel-replay step is the deeper backstop)" r2
    let exists_ ← (candidatePath wd).pathExists
    check statsRef (!exists_) "A27 no candidate.lean (removed after gate rejection)"
    let st ← s.call "state"
    check statsRef (!contains st "PROOF COMPLETE") "A27 rollback happened: not complete" st

-- A28 default configuration, Rocq parity with NO environment variables set
-- ON THE AXIS THAT IS STILL GATED: all nine tools enabled, no up-front
-- `import` refusal (LEAN_ENV_V2 off by default, exactly like ROCQ_ENV_V2 --
-- `import Mathlib` is just an ordinary tactic error, not a refusal), no
-- in-session gate (LEAN_GATE off by default). The `sorry` refusal is
-- UNCONDITIONAL, though (restored 2026-09-08 -- see A7's doc comment): it is
-- refused here exactly as under `LEAN_ENV_V2=1`, so it does NOT yield PROOF
-- COMPLETE or a written candidate even by default. Nothing set except
-- LEAN_WORKDIR (no LEAN_TASK_FILE preset either, so `open` is exercised at
-- runtime, as in A12).
def a28 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "sessA_"
  let n ← freshSuffix
  let f := proj / "Coreproj" / s!"T28_{n}.lean"
  let content ← fixture "F2.lean"
  writeFile f content
  withServerEnv proj [("LEAN_WORKDIR", wd.toString)] fun s => do
    let r0 ← s.call "open" (Json.mkObj [("file", f.toString)])
    check statsRef (contains r0 "proving t2") "A28 open by path with no LEAN_TASK_FILE preset" r0
    let r1 ← s.call "step" (Json.mkObj [("text", "import Mathlib")])
    check statsRef (!contains r1 "not allowed") "A28 import NOT refused by default (LEAN_ENV_V2 unset)" r1
    check statsRef (!contains r1 "PROOF COMPLETE") "A28 import Mathlib is just an ordinary tactic error" r1
    let r2 ← s.call "step" (Json.mkObj [("text", "sorry")])
    check statsRef (contains r2 "`sorry` is not allowed") "A28 sorry refused by default too (unconditional refusal)" r2
    check statsRef (!contains r2 "PROOF COMPLETE") "A28 sorry does not complete by default either" r2
    let exists_ ← (candidatePath wd).pathExists
    check statsRef (!exists_) "A28 no candidate.lean by default either (sorry refused)"

-- A29 server candidate passes the gate with --reference: the real harness
-- flow (server writes `candidate.lean`; the harness then runs the standalone
-- gate with the ORIGINAL task file as `--reference`) must ACCEPT a genuine
-- proof. Before the `Driver.candidateText` fix, the written candidate was
-- not byte-identical to the task file outside the target's proof (a stray
-- extra newline before the captured tail, and using the statement's
-- normalised -- right-trimmed, `" := by"`-suffixed -- form instead of the
-- original's raw bytes up to `:=`), so this reference comparison spuriously
-- rejected with `suffix_modified`/`prefix_modified`. Each case below exists
-- to exercise one shape that could desync the candidate from the reference:
-- (a) the base single-declaration case; (b)/(c) a sibling declaration after
-- / before the target (exercises `tailText`/`prefixText` on a non-empty
-- neighbour); (d) a term-style `:= sorry` original (statement gets
-- re-cast into `by`-form); (e) a folded `set_option ... in` prefix; (f) a
-- doc comment + attribute above the target; (g) no trailing newline in the
-- file at all (the empty-tail edge case that most directly showed the
-- extra-newline bug); (h) an original proof spanning several lines (so
-- `endPos` must land after the LAST line of the old proof, not the first).
structure A29Case where
  label       : String
  content     : String
  theoremName : String
  tacticText  : String

def a29Cases : List A29Case := [
  { label := "a", content := "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n",
    theoremName := "t2", tacticText := "omega" },
  { label := "b", content :=
      "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n\ntheorem t3 : True := by\n  sorry\n",
    theoremName := "t2", tacticText := "omega" },
  { label := "c", content :=
      "theorem t3 : True := by\n  sorry\n\ntheorem t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n",
    theoremName := "t2", tacticText := "omega" },
  { label := "d", content := "theorem t4 (n : Nat) : n + 0 = n := sorry\n",
    theoremName := "t4", tacticText := "rfl" },
  { label := "e", content := "set_option maxRecDepth 1000 in\ntheorem t5 : True := by\n  sorry\n",
    theoremName := "t5", tacticText := "trivial" },
  { label := "f", content := "/-- doc -/\n@[simp]\ntheorem t6 (n : Nat) : n + 0 = n := by\n  sorry\n",
    theoremName := "t6", tacticText := "omega" },
  { label := "g", content := "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry",
    theoremName := "t2", tacticText := "omega" },
  { label := "h", content :=
      "theorem t7 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  · sorry\n  · sorry\n",
    theoremName := "t7", tacticText := "exact ⟨hp, hq⟩" } ]

/-- `orig[0 : target.stmtEndPos]` and `orig[target.endPos : end]` -- the two
regions `candidateText` must reproduce byte-for-byte -- located with the very
same `LeanMcpEvolve.Text.findDecls`/`findDecl` the production code and the
gate both use (rather than a hand-rolled string search, which would need its
own logic to skip a *preceding* declaration's `:=` in cases (b)/(c)). -/
def a29ExpectedBeforeAfter (content theoremName : String) : IO (String × String) := do
  -- `findDecls` parses `content` for real (`processHeader` on an implicit
  -- `import Init`), which needs the Lean sysroot on the search path -- set up
  -- by `Driver.initSearchPath` inside the (separate) server process this
  -- suite spawns, but never inside THIS test-binary process itself. Without
  -- this, `findDecls` here (unlike the server's own, correctly-initialized
  -- call) mis-parses the command and returns a bogus, truncated `Decl`
  -- (compare `Tests.Text.mkEnv`, which needs the exact same call for the same
  -- reason).
  Lean.initSearchPath (← Lean.findSysroot)
  let decls ← LeanMcpEvolve.Text.findDecls content
  match LeanMcpEvolve.Text.findDecl decls theoremName with
  | none => throw (IO.userError s!"A29: '{theoremName}' not found by Text.findDecls in fixture: {content}")
  | some d =>
    let before := String.Pos.Raw.extract content ⟨0⟩ d.stmtEndPos
    let after := String.Pos.Raw.extract content d.endPos content.rawEndPos
    pure (before, after)

def a29One (statsRef : IO.Ref Stats) (c : A29Case) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "sessA_"
  let n ← freshSuffix
  let f := proj / "Coreproj" / s!"T29{c.label}_{n}.lean"
  writeFile f c.content
  withServerEnv proj [("LEAN_WORKDIR", wd.toString)] fun s => do
    let r0 ← s.call "open" (Json.mkObj [("file", f.toString), ("theorem", c.theoremName)])
    check statsRef (contains r0 s!"proving {c.theoremName}") s!"A29{c.label} open theorem:{c.theoremName}" r0
    let r1 ← s.call "step" (Json.mkObj [("text", c.tacticText)])
    check statsRef (contains r1 "PROOF COMPLETE") s!"A29{c.label} {c.tacticText} yields PROOF COMPLETE" r1
    let exists_ ← (candidatePath wd).pathExists
    check statsRef exists_ s!"A29{c.label} candidate.lean exists"
    if exists_ then
      let candContent ← readFile (candidatePath wd)
      let (expectedBefore, expectedAfter) ← a29ExpectedBeforeAfter c.content c.theoremName
      check statsRef (candContent.startsWith expectedBefore)
        s!"A29{c.label} candidate prefix (before target's :=) byte-identical to the original" candContent
      check statsRef (candContent.endsWith expectedAfter)
        s!"A29{c.label} candidate suffix (after target's endPos) byte-identical to the original" candContent
      let gr ← runGateCli proj (candidatePath wd) c.theoremName (some f)
      check statsRef (gr.exitCode == 0) s!"A29{c.label} gate exit 0 with --reference" gr.stdout
      check statsRef (contains gr.stdout "ACCEPTED") s!"A29{c.label} gate ACCEPTED with --reference" gr.stdout

def a29 (statsRef : IO.Ref Stats) : IO Unit := do
  for c in a29Cases do
    a29One statsRef c

-- A30 eager open (Fix 2 / docs/PLAN.md): with `LEAN_TASK_FILE` preset, the
-- open starts in the BACKGROUND at server startup, not lazily on the first
-- tool call -- so the first call here is `state`, never `open`, and it must
-- already return the goal; the JSONL log (`LEAN_LOG_FILE`) must show
-- exactly one open in total (one `eager_open` record, and no `open`
-- tool_call, since `open` itself was never invoked).
def a30 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  let logf := wd / "log.jsonl"
  withServer wd tf "state" [("LEAN_LOG_FILE", logf.toString)] fun s => do
    let r ← s.call "state"
    check statsRef (contains r "proving t2") "A30 first state call returns the already-opened goal" r
    check statsRef (contains r "goals: 1") "A30 first state call shows the goal (no second, redundant open needed)" r
    let content ← readFile logf
    let lines := (content.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
    let recs := lines.filterMap (fun l => (Json.parse l).toOption)
    let eagerOpens := recs.filter (fun r => r.getObjValD "kind" == Json.str "eager_open")
    let explicitOpens := recs.filter (fun r =>
      r.getObjValD "kind" == Json.str "tool_call" && r.getObjValD "tool" == Json.str "open")
    check statsRef ((eagerOpens.length + explicitOpens.length) == 1)
      "A30 exactly one open (eager + explicit) in the log" s!"{recs}"
    check statsRef (eagerOpens.length == 1) "A30 exactly one eager_open record" s!"{recs}"
    check statsRef (explicitOpens.isEmpty) "A30 no explicit open tool_call (state alone triggered it)" s!"{recs}"

-- A31 eager-open failure (Fix 2): a bad `LEAN_TASK_FILE` preset must
-- surface as the SAME error text the lazy path produces today (`no such
-- file: ...`), reported on the first tool call rather than crashing the
-- server -- and the server must still be usable afterwards (a fresh
-- explicit `open` on a real file works).
def a31 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "sessA_"
  let n ← freshSuffix
  let bogus := proj / "Coreproj" / s!"A31Missing{n}.lean"
  withServerEnv proj [("LEAN_TASK_FILE", bogus.toString), ("LEAN_WORKDIR", wd.toString)] fun s => do
    let r ← s.call "state"
    check statsRef (contains r "no such file") "A31 bad preset reported as error on the first tool call" r
    let f := proj / "Coreproj" / s!"A31Real{n}.lean"
    writeFile f "theorem a31real (n : Nat) : n = n := by\n  sorry\n"
    let r2 ← s.call "open" (Json.mkObj [("file", f.toString)])
    check statsRef (contains r2 "proving a31real") "A31 server still usable after the bad preset (not crashed)" r2

-- A32 header-environment cache (README "Excluding Mathlib import time from
-- attempt budgets"): open a file A (no `LEAN_TASK_FILE` preset -- runtime
-- `open`, as in A12/A28), then a DIFFERENT file B with the SAME (here:
-- empty) import list. Each `open` call fetches its header exactly once
-- (`Driver.openFile`'s single `headerR0` fetch, reused by prefix processing
-- when there's no preload -- see its doc comment), so the log must show
-- exactly one `import` record per open: two total, the second `cached:
-- true`, and the second open's own `tool_call` record must show it barely
-- waited on anything (`import_ms` a few ms at most -- purely the cache
-- lookup, not a real header load).
def a32 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "sessA_"
  let n ← freshSuffix
  let fA := proj / "Coreproj" / s!"T32A_{n}.lean"
  let fB := proj / "Coreproj" / s!"T32B_{n}.lean"
  let content ← fixture "F2.lean"
  writeFile fA content
  writeFile fB content
  let logf := wd / "log.jsonl"
  withServerEnv proj [("LEAN_WORKDIR", wd.toString), ("LEAN_LOG_FILE", logf.toString)] fun s => do
    let r1 ← s.call "open" (Json.mkObj [("file", fA.toString)])
    check statsRef (contains r1 "proving t2") "A32 open file A" r1
    let r2 ← s.call "open" (Json.mkObj [("file", fB.toString)])
    check statsRef (contains r2 "proving t2") "A32 open file B (same import list)" r2
    let content2 ← readFile logf
    let lines := (content2.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
    let recs := lines.filterMap (fun l => (Json.parse l).toOption)
    let importRecs := recs.filter (fun r => r.getObjValD "kind" == Json.str "import")
    check statsRef (importRecs.length == 2) "A32 exactly two import records (one per open)" s!"{importRecs}"
    match importRecs with
    | first :: second :: _ =>
      check statsRef (first.getObjValD "cached" == Json.bool false)
        "A32 first import record cached:false (genuine header load)" s!"{first}"
      check statsRef (second.getObjValD "cached" == Json.bool true)
        "A32 second import record cached:true (same import list, file B)" s!"{second}"
    | _ => check statsRef false "A32 two import records present" s!"{importRecs}"
    let openCalls := recs.filter (fun r =>
      r.getObjValD "kind" == Json.str "tool_call" && r.getObjValD "tool" == Json.str "open")
    match openCalls with
    | _ :: secondOpen :: _ =>
      let importMs := getFloatField secondOpen "import_ms"
      check statsRef (importMs < 200.0)
        "A32 second open's tool_call import_ms ≈ 0 (< 200ms, header was cached)" s!"{secondOpen}"
    | _ => check statsRef false "A32 second open's tool_call record present" s!"{recs}"

-- A33 prewarm (README "Excluding Mathlib import time from attempt budgets"):
-- with `LEAN_TASK_FILE` preset and `LEAN_LOG_FILE` set, `initialize` must
-- answer fast (the header-only prewarm task, plus the existing eager-open,
-- both run in the BACKGROUND, never blocking the handshake); after the
-- first tool call, the log must carry an `import` record tagged
-- `prewarm: true` (the background task's own header load, which the eager
-- open's `open` then simply waited on / hit in cache -- see
-- `Driver.acquireHeaderState`), the tool call's own `tool_call` record must
-- carry `import_ms`, and on exit the log must carry a `shutdown` record with
-- `import_ms_total`.
def a33 (statsRef : IO.Ref Stats) : IO Unit := do
  let (wd, tf) ← setupTask "F2.lean"
  let logf := wd / "log.jsonl"
  let proj ← coreProject
  let sChild ← spawnServer proj
    [("LEAN_TASK_FILE", tf.toString), ("LEAN_WORKDIR", wd.toString), ("LEAN_LOG_FILE", logf.toString)]
  let t0 ← IO.monoMsNow
  let _ ← sChild.initialize
  let t1 ← IO.monoMsNow
  check statsRef ((t1 - t0) < 2000)
    "A33 initialize returns in <2s with LEAN_TASK_FILE+LEAN_LOG_FILE set" s!"{t1 - t0}ms"
  let r ← sChild.call "step" (Json.mkObj [("text", "omega")])
  check statsRef (contains r "PROOF COMPLETE") "A33 first tool call (step) completes" r
  sChild.close
  let content ← readFile logf
  let lines := (content.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
  let recs := lines.filterMap (fun l => (Json.parse l).toOption)
  let prewarmImports := recs.filter (fun r =>
    r.getObjValD "kind" == Json.str "import" && r.getObjValD "prewarm" == Json.bool true)
  check statsRef (!prewarmImports.isEmpty) "A33 at least one import record with prewarm:true" s!"{recs}"
  match recs.find? (fun r => r.getObjValD "kind" == Json.str "tool_call" && r.getObjValD "tool" == Json.str "step") with
  | none => check statsRef false "A33 step's tool_call record present" s!"{recs}"
  | some tc =>
    check statsRef (((tc.getObjValD "import_ms").getNum?).toOption.isSome)
      "A33 step's tool_call record carries import_ms" s!"{tc}"
  let shutdowns := recs.filter (fun r => r.getObjValD "kind" == Json.str "shutdown")
  check statsRef (!shutdowns.isEmpty) "A33 shutdown record present on exit" s!"{recs}"
  match shutdowns.head? with
  | some sd =>
    check statsRef (((sd.getObjValD "import_ms_total").getNum?).toOption.isSome)
      "A33 shutdown record carries import_ms_total" s!"{sd}"
  | none => pure ()

def run (statsRef : IO.Ref Stats) : IO Unit := do
  runCase statsRef "A0" a0
  runCase statsRef "A1" a1
  runCase statsRef "A2" a2
  runCase statsRef "A3" a3
  runCase statsRef "A3b" a3b
  runCase statsRef "A4" a4
  runCase statsRef "A4b" a4b
  runCase statsRef "A6" a6
  runCase statsRef "A7" a7
  runCase statsRef "A7b" a7b
  runCase statsRef "A8" a8
  runCase statsRef "A9" a9
  runCase statsRef "A12" a12
  runCase statsRef "A14" a14
  runCase statsRef "A15" a15
  runCase statsRef "A16" a16
  runCase statsRef "A17" a17
  runCase statsRef "A18" a18
  runCase statsRef "A19" a19
  runCase statsRef "A20" a20
  runCase statsRef "A21" a21
  runCase statsRef "A22" a22
  runCase statsRef "A23" a23
  runCase statsRef "A24" a24
  runCase statsRef "A25" a25
  runCase statsRef "A27" a27
  runCase statsRef "A28" a28
  runCase statsRef "A29" a29
  runCase statsRef "A30" a30
  runCase statsRef "A31" a31
  runCase statsRef "A32" a32
  runCase statsRef "A33" a33

end Tests.Session
