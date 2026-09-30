/-
Tests.Mathlib — suite M: Mathlib-backed contracts, ported case-for-case from
`prototype-python/tests/test_mathlib.py` (see `prototype-python/tests/ARCHITECTURE.md`'s
"suite M" section). Skipped unless `LEAN_MCP_TEST_MATHLIB_PROJECT` points at a
built Lean project depending on Mathlib; fixtures are written into a scratch
subdirectory of it (`LeanMcpEvolveTests/`), removed when the suite finishes.
-/
import Tests.Helpers

namespace Tests.Mathlib

open Lean (Json)
open Tests.Helpers (Server Stats check contains mathlibProject writeFile readFile tmpdir spawnServer repoRoot getFloatField)

/-- Absolute path to the built `gate` executable (same convention as
`Tests.Session.gateBinPath`/`Tests.Gate.gateBinPath`). -/
def gateBinPath : IO System.FilePath := do
  pure ((← repoRoot) / ".lake" / "build" / "bin" / "gate")

structure GateCliResult where
  exitCode : UInt32
  stdout   : String

/-- Run the `gate` executable as a subprocess, `lake env`-wrapped from `proj`
(the Mathlib-backed project, so its own `LEAN_PATH` resolves) with
`--reference` given, mirroring `Tests.Session.runGateCli`. -/
def runGateCli (proj cand reference : System.FilePath) (theoremName : String) : IO GateCliResult := do
  let bin ← gateBinPath
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", bin.toString, cand.toString, "--theorem", theoremName,
      "--reference", reference.toString, "--project", proj.toString]
    cwd := some proj }
  pure { exitCode := out.exitCode, stdout := out.stdout }

def scratchDirName : String := "LeanMcpEvolveTests"

/-- Write `content` into the Mathlib project's scratch directory as `name`,
and return `(workdir, taskfile)` — port of Python's `MathlibTests.task`. -/
def mtask (proj : System.FilePath) (name content : String) : IO (System.FilePath × System.FilePath) := do
  let wd ← tmpdir "sessM_"
  let f := proj / scratchDirName / name
  writeFile f content
  pure (wd, f)

def spawn (proj wd : System.FilePath) (extra : List (String × String) := []) : IO Server := do
  let s ← spawnServer proj (("LEAN_WORKDIR", wd.toString) :: extra)
  let _ ← s.initialize
  pure s

def withServer (proj wd : System.FilePath) (extra : List (String × String) := [])
    (body : Server → IO Unit) : IO Unit := do
  let s ← spawn proj wd extra
  try body s finally s.close

/-- Run one test case, catching any uncaught exception as a single FAIL
rather than aborting the rest of the suite (mirrors `Tests.Session.runCase`). -/
def runCase (statsRef : IO.Ref Stats) (name : String) (action : IO.Ref Stats → IO Unit) : IO Unit := do
  try
    action statsRef
  catch e =>
    check statsRef false s!"{name} (uncaught exception)" s!"{e}"

-- M1 hint synthesis (rung 9b): the pow2 hint closes the F1 goal
def m1 (statsRef : IO.Ref Stats) (proj : System.FilePath) : IO Unit := do
  let content ← Tests.Helpers.fixture "F1.lean"
  let (wd, f) ← mtask proj "M1.lean" content
  withServer proj wd [("LEAN_AUTO2", "1"), ("LEAN_AUTO_SEARCH", "0")] fun s => do
    let r ← s.call "open" (Json.mkObj [("file", f.toString), ("theorem", "t1")])
    check statsRef (contains r "⊢ (x ^ 6 + 1) / 2 ≥ x ^ 3") "M1 goal shown" r
    let r2 ← s.call "auto_close"
    check statsRef (contains r2 "COMMITTED") "M1 COMMITTED" r2
    check statsRef (contains r2 "PROOF COMPLETE") "M1 PROOF COMPLETE" r2
    check statsRef (contains r2 "nlinarith [") "M1 synthesized nlinarith" r2
    check statsRef (contains r2 "sq_nonneg (x ^ 3 - 1)") "M1 sq_nonneg hint" r2
    let cand ← readFile (wd / "candidate.lean")
    check statsRef (contains cand "nlinarith") "M1 candidate.lean contains nlinarith" cand

-- M2 Rocq-isms at a Mathlib goal: nra hint, Coq lemma-name hint, try with
-- Mathlib closers commits the working candidate
def m2 (statsRef : IO.Ref Stats) (proj : System.FilePath) : IO Unit := do
  let content ← Tests.Helpers.fixture "F1.lean"
  let (wd, f) ← mtask proj "M2.lean" content
  withServer proj wd [] fun s => do
    let _ ← s.call "open" (Json.mkObj [("file", f.toString), ("theorem", "t1")])
    let r ← s.call "step" (Json.mkObj [("text", "nra")])
    check statsRef (contains r "SYNTAX ERROR") "M2 nra is a syntax error" r
    check statsRef (contains r "nlinarith") "M2 nra hint mentions nlinarith" r
    let r2 ← s.call "step" (Json.mkObj [("text", "apply Rmult_le_pos")])
    check statsRef (contains r2 "Rocq/Coq lemma name") "M2 Rocq/Coq lemma name hint" r2
    let cands := Json.arr (#["nlinarith", "positivity", "have h := sq_nonneg (x^3 - 1)\nnlinarith"].map Json.str)
    let r3 ← s.call "try" (Json.mkObj [("candidates", cands)])
    check statsRef (contains r3 "[1] `nlinarith` — error") "M2 [1] nlinarith error" r3
    check statsRef (contains r3 "[3]") "M2 [3] present" r3
    check statsRef (contains r3 "<< COMMITTED") "M2 a working candidate committed" r3
    check statsRef (contains r3 "PROOF COMPLETE") "M2 PROOF COMPLETE" r3

-- M3 preloading (A11 analogue): a file importing only part of Mathlib gets
-- `import Mathlib.Tactic` for the session, and completion echoes it; with
-- LEAN_PRELOAD=0 the tactic is unknown and unavailable closers are skipped
def m3 (statsRef : IO.Ref Stats) (proj : System.FilePath) : IO Unit := do
  let content :=
    "import Mathlib.Data.Real.Basic\n\ntheorem t4 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x + y := by\n  sorry\n"
  let (wd, f) ← mtask proj "M3.lean" content
  withServer proj wd [] fun s => do
    let r ← s.call "open" (Json.mkObj [("file", f.toString)])
    check statsRef (contains r "proving t4") "M3 proving t4" r
    let r2 ← s.call "step" (Json.mkObj [("text", "linarith")])
    check statsRef (contains r2 "PROOF COMPLETE") "M3 linarith completes (preloaded)" r2
    check statsRef (contains r2 "IMPORTANT: this proof uses linarith") "M3 import echo warning" r2
    check statsRef (contains r2 "import Mathlib.Tactic") "M3 import echo shows the import line" r2
    let c ← readFile (wd / "candidate.lean")
    check statsRef (contains c "import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic")
      "M3 candidate carries the injected import" c
    check statsRef (contains c "linarith") "M3 candidate contains linarith" c
  let wd2 ← tmpdir "sessM_"
  withServer proj wd2 [("LEAN_PRELOAD", "0"), ("LEAN_AUTO_SEARCH", "0")] fun s2 => do
    let _ ← s2.call "open" (Json.mkObj [("file", f.toString)])
    let r ← s2.call "step" (Json.mkObj [("text", "linarith")])
    check statsRef (contains r "unknown tactic") "M3 (preload off) linarith is unknown" r
    let r2 ← s2.call "auto_close"
    check statsRef (contains r2 "COMMITTED" || contains r2 "no finisher applies")
      "M3 (preload off) auto_close: real closure or honest miss" r2
    if contains r2 "no finisher applies" then
      let firstLine := (r2.splitOn "\n").headD ""
      check statsRef (!contains firstLine "linarith")
        "M3 (preload off) unavailable closers not even tried (not in first line)" r2

-- M4 search tactic inside a bullet is committed as its suggestion
def m4 (statsRef : IO.Ref Stats) (proj : System.FilePath) : IO Unit := do
  let content := "import Mathlib\n\ntheorem t5 (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 ∧ b ≤ b + 2 := by\n  sorry\n"
  let (wd, f) ← mtask proj "M4.lean" content
  withServer proj wd [] fun s => do
    let _ ← s.call "open" (Json.mkObj [("file", f.toString), ("theorem", "t5")])
    let r ← s.call "step" (Json.mkObj [("text", "constructor\n· omega\n· exact?")])
    check statsRef (contains r "PROOF COMPLETE") "M4 PROOF COMPLETE" r
    let c ← readFile (wd / "candidate.lean")
    check statsRef (!contains c "exact?") "M4 candidate has the found tactic, not exact? literally" c

-- M5 build on a Mathlib file, then open a hole and close it
def m5 (statsRef : IO.Ref Stats) (proj : System.FilePath) : IO Unit := do
  let content :=
    "import Mathlib\n\ntheorem k1 (x : ℝ) : x ≤ x + 1 := by\n  nra\n\n" ++
    "theorem k2 (x : ℝ) : x ^ 2 ≥ 0 := by\n  sorry\n\n" ++
    "theorem k3 (x : ℝ) : x ≤ x + 1 := by\n  linarith\n"
  let (wd, f) ← mtask proj "M5.lean" content
  withServer proj wd [] fun s => do
    let r ← s.call "build" (Json.mkObj [("file", f.toString)])
    check statsRef (contains r "1 declaration(s) OK, 2 hole(s)") "M5 build summary" r
    check statsRef (contains r "- k1:") "M5 k1 listed (nra is not a tactic)" r
    check statsRef (contains r "- k2: uses `sorry`") "M5 k2 uses sorry" r
    let r2 ← s.call "open" (Json.mkObj [("file", f.toString), ("theorem", "k2")])
    check statsRef (contains r2 "proving k2") "M5 proving k2" r2
    let r3 ← s.call "step" (Json.mkObj [("text", "positivity")])
    check statsRef (contains r3 "PROOF COMPLETE") "M5 positivity completes k2" r3

-- M6 the real harness flow with Mathlib preload: the server's own candidate
-- (after the `Driver.candidateText` fix, see `Tests.Session`'s A29) must
-- pass the standalone gate run with `--reference` pointed at the ORIGINAL
-- task file -- the one case A29 cannot cover on the core project, since it
-- specifically exercises `Gate.checkTamper`'s tolerated-header-addition path
-- (`dropOneMathlibImportLine`): the task file doesn't import `Mathlib.Tactic`
-- itself, so `linarith` only works because the session preloads it, and that
-- one extra header line is the single difference the gate is meant to
-- tolerate between candidate and reference.
def m6 (statsRef : IO.Ref Stats) (proj : System.FilePath) : IO Unit := do
  let content :=
    "import Mathlib.Data.Real.Basic\n\n" ++
    "theorem t8 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x + y := by\n  sorry\n"
  let (wd, f) ← mtask proj "M6.lean" content
  withServer proj wd [] fun s => do
    let r ← s.call "open" (Json.mkObj [("file", f.toString), ("theorem", "t8")])
    check statsRef (contains r "proving t8") "M6 proving t8" r
    let r2 ← s.call "step" (Json.mkObj [("text", "linarith")])
    check statsRef (contains r2 "PROOF COMPLETE") "M6 linarith completes (preloaded)" r2
    let candPath := wd / "candidate.lean"
    let exists_ ← candPath.pathExists
    check statsRef exists_ "M6 candidate.lean exists"
    if exists_ then
      let gr ← runGateCli proj candPath f "t8"
      check statsRef (gr.exitCode == 0) "M6 gate exit 0 with --reference" gr.stdout
      check statsRef (contains gr.stdout "ACCEPTED")
        "M6 gate ACCEPTED with --reference (tolerated import Mathlib.Tactic addition)" gr.stdout

-- M7 header-environment cache pays `import Mathlib` once per process
-- (README "Excluding Mathlib import time from attempt budgets"): open F1
-- (`import Mathlib`), then a SECOND file with the same `import Mathlib`
-- header. The second open must be a header cache hit: its `import` JSONL
-- record is `cached: true`, and its `tool_call` record's `import_ms` is
-- nowhere near a real `import Mathlib` cost (asserted generously, < 2s, to
-- stay robust on a loaded CI machine -- the point is "not tens of seconds
-- again", not a tight bound). Prints both durations for the task report.
def m7 (statsRef : IO.Ref Stats) (proj : System.FilePath) : IO Unit := do
  let content ← Tests.Helpers.fixture "F1.lean"
  let (wd, fA) ← mtask proj "M7A.lean" content
  let fB := proj / scratchDirName / "M7B.lean"
  writeFile fB content
  let logf := wd / "log.jsonl"
  withServer proj wd [("LEAN_LOG_FILE", logf.toString)] fun s => do
    let r1 ← s.call "open" (Json.mkObj [("file", fA.toString), ("theorem", "t1")])
    check statsRef (contains r1 "proving t1") "M7 open file A (import Mathlib)" r1
    let r2 ← s.call "open" (Json.mkObj [("file", fB.toString), ("theorem", "t1")])
    check statsRef (contains r2 "proving t1") "M7 open file B (same import list)" r2
    let content2 ← readFile logf
    let lines := (content2.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
    let recs := lines.filterMap (fun l => (Json.parse l).toOption)
    let importRecs := recs.filter (fun r => r.getObjValD "kind" == Json.str "import")
    check statsRef (importRecs.length ≥ 2) "M7 at least two import records" s!"{importRecs.length}"
    match importRecs with
    | first :: second :: _ =>
      let d1 := getFloatField first "dur_ms"
      let d2 := getFloatField second "dur_ms"
      IO.println s!"M7 first import (file A): dur_ms={d1} cached={first.getObjValD "cached"}"
      IO.println s!"M7 second import (file B): dur_ms={d2} cached={second.getObjValD "cached"}"
      check statsRef (second.getObjValD "cached" == Json.bool true)
        "M7 second import record cached:true" s!"{second}"
    | _ => check statsRef false "M7 two import records present" s!"{importRecs}"
    let openCalls := recs.filter (fun r =>
      r.getObjValD "kind" == Json.str "tool_call" && r.getObjValD "tool" == Json.str "open")
    match openCalls with
    | _ :: secondOpen :: _ =>
      let importMs := getFloatField secondOpen "import_ms"
      IO.println s!"M7 second open's tool_call import_ms={importMs}"
      check statsRef (importMs < 2000.0)
        "M7 second open's tool_call import_ms < 2000ms (cached, not a real Mathlib import)" s!"{secondOpen}"
    | _ => check statsRef false "M7 second open's tool_call record present" s!"{recs}"

-- M8 prewarm on the Mathlib project: `LEAN_PREWARM_IMPORTS=Mathlib` plus a
-- `LEAN_TASK_FILE` preset -- `initialize` must still answer fast (the
-- ~40-120s `import Mathlib` runs entirely in the background), and after the
-- task file's `open` the log must carry an `import` record tagged
-- `prewarm: true`. The test calls `open` immediately after `initialize`
-- (not waiting for the background import to finish first), so it may itself
-- have to wait on the prewarm task mid-call -- only the record's presence
-- and a successful open are asserted, not a tight `import_ms` bound (see
-- the task description this test is ported from).
def m8 (statsRef : IO.Ref Stats) (proj : System.FilePath) : IO Unit := do
  let content ← Tests.Helpers.fixture "F1.lean"
  let (wd, f) ← mtask proj "M8.lean" content
  let logf := wd / "log.jsonl"
  let sChild ← spawnServer proj
    [ ("LEAN_WORKDIR", wd.toString), ("LEAN_TASK_FILE", f.toString)
    , ("LEAN_PREWARM_IMPORTS", "Mathlib"), ("LEAN_LOG_FILE", logf.toString) ]
  let t0 ← IO.monoMsNow
  let _ ← sChild.initialize
  let t1 ← IO.monoMsNow
  -- The bound here is generous (15s, not the 2s A33 uses on the tiny core
  -- project) because `spawnServer` launches the child via `lake env <bin>`,
  -- and `lake env`'s OWN process-launch/dependency-resolution overhead on a
  -- full Mathlib project is itself a few seconds, dominating this
  -- measurement -- unrelated to whether `initialize` blocks on the import.
  -- What this assertion actually rules out is `initialize` waiting on the
  -- ~40-120s `import Mathlib` itself (measured standalone in M7: single
  -- digits to low tens of seconds warm, tens cold) -- 15s is still a wide
  -- margin below that.
  check statsRef ((t1 - t0) < 15000)
    "M8 initialize returns well under the import's own cost despite LEAN_PREWARM_IMPORTS=Mathlib"
    s!"{t1 - t0}ms"
  let r ← sChild.call "open" (Json.mkObj [("file", f.toString), ("theorem", "t1")])
  check statsRef (contains r "proving t1") "M8 open succeeds" r
  sChild.close
  let content2 ← readFile logf
  let lines := (content2.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
  let recs := lines.filterMap (fun l => (Json.parse l).toOption)
  let prewarmImports := recs.filter (fun r =>
    r.getObjValD "kind" == Json.str "import" && r.getObjValD "prewarm" == Json.bool true)
  check statsRef (!prewarmImports.isEmpty) "M8 at least one import record with prewarm:true" s!"{recs.length} records"

def run (statsRef : IO.Ref Stats) : IO Unit := do
  match ← mathlibProject with
  | none => IO.println "ok - SKIP suite M (no LEAN_MCP_TEST_MATHLIB_PROJECT)"
  | some proj =>
    let scratch := proj / scratchDirName
    IO.FS.createDirAll scratch
    try
      runCase statsRef "M1" (fun st => m1 st proj)
      runCase statsRef "M2" (fun st => m2 st proj)
      runCase statsRef "M3" (fun st => m3 st proj)
      runCase statsRef "M4" (fun st => m4 st proj)
      runCase statsRef "M5" (fun st => m5 st proj)
      runCase statsRef "M6" (fun st => m6 st proj)
      runCase statsRef "M7" (fun st => m7 st proj)
      runCase statsRef "M8" (fun st => m8 st proj)
    finally
      try IO.FS.removeDirAll scratch catch _ => pure ()

end Tests.Mathlib
