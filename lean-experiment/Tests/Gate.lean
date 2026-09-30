/-
Tests.Gate — suite D: the correctness GATE (`LeanMcpEvolve.Gate`), the
anti-gaming analogue of rocq-mcp-evolve's `harness/gate.py` tests. Each case
writes a reference/candidate pair (or just a candidate) into a fresh temp
directory, runs the built `gate` executable as a *subprocess* (`lake env
<abs .lake/build/bin/gate> ...`, from the core project directory, so
`LEAN_PATH` resolves exactly as it would for a real invocation), and asserts
on the CLI's `ACCEPTED` / `REJECTED: <reason>` line and exit code; several
cases also drive the library API `LeanMcpEvolve.Gate.run`/`runInternal`
directly (in-process) for the "defense in depth" checks, since those need to
disable the forbidden-token check to prove steps 3-6 independently reject
what step 2 would already have caught.

Every case is wrapped in `runCase` (same contract as `Tests.Session`'s): an
uncaught exception becomes a single FAIL rather than aborting the suite.
-/
import Tests.Helpers
import LeanMcpEvolve.Gate

namespace Tests.Gate

open Tests.Helpers (Stats check contains coreProject tmpdir writeFile repoRoot)
open LeanMcpEvolve

/-- Absolute path to the built `gate` executable. -/
def gateBinPath : IO System.FilePath := do
  pure ((← repoRoot) / ".lake" / "build" / "bin" / "gate")

structure CliResult where
  exitCode : UInt32
  stdout   : String
  stderr   : String

/-- Run the `gate` executable as a subprocess, `lake env`-wrapped from `cwd`
(the core project directory, so its own `LEAN_PATH` resolves) -- mirrors how
a real harness would invoke it, per the task briefing ("invoke the gate as a
subprocess `lake env <abs .lake/build/bin/gate> …`"). -/
def runGateCli (cwd : System.FilePath) (args : Array String) : IO CliResult := do
  let bin ← gateBinPath
  let out ← IO.Process.output { cmd := "lake", args := #["env", bin.toString] ++ args, cwd := some cwd }
  pure { exitCode := out.exitCode, stdout := out.stdout, stderr := out.stderr }

/-- Run one test case, catching any uncaught exception as a single FAIL
(same contract as `Tests.Session.runCase`). -/
def runCase (statsRef : IO.Ref Stats) (name : String) (action : IO.Ref Stats → IO Unit) : IO Unit := do
  try
    action statsRef
  catch e =>
    check statsRef false s!"{name} (uncaught exception)" s!"{e}"

-- D1 legit accept (regresses: a genuine closer must still pass every gate --
-- tamper/token/compile/type/axiom/kernel-replay -- not just the in-session check)
def d1 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "gateD1_"
  let refPath := wd / "reference.lean"
  let candPath := wd / "candidate.lean"
  writeFile refPath "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n"
  writeFile candPath "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  omega\n"
  let r ← runGateCli proj #[candPath.toString, "--theorem", "t2", "--reference", refPath.toString, "--project", proj.toString]
  check statsRef (r.exitCode == 0) "D1 CLI exit 0" s!"{r.stdout}\n{r.stderr}"
  check statsRef (contains r.stdout "ACCEPTED") "D1 CLI ACCEPTED" r.stdout
  let v ← Gate.run candPath "t2" (some refPath) (some proj)
  check statsRef v.accepted "D1 library accepted" v.reason
  check statsRef (v.axioms.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound))
    "D1 library axioms ⊆ standard" s!"{v.axioms}"

-- D2 placeholders (regresses: an in-session-looking "success" that is really
-- a give-up must still be rejected, both by the token scan and, if that were
-- ever bypassed, by the axiom/sorry-warning check independently)
def d2 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "gateD2_"
  let p1 := wd / "c1.lean"
  writeFile p1 "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n"
  let r1 ← runGateCli proj #[p1.toString, "--theorem", "t2", "--project", proj.toString]
  check statsRef (r1.exitCode == 1) "D2 sorry CLI exit 1"
  check statsRef (contains r1.stdout "REJECTED: forbidden_token:sorry") "D2 sorry forbidden_token:sorry" r1.stdout
  let p2 := wd / "c2.lean"
  writeFile p2 "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  exact sorryAx _ false\n"
  let r2 ← runGateCli proj #[p2.toString, "--theorem", "t2", "--project", proj.toString]
  check statsRef (r2.exitCode == 1) "D2 sorryAx CLI exit 1"
  check statsRef (contains r2.stdout "REJECTED: forbidden_token:sorryAx") "D2 sorryAx forbidden_token:sorryAx" r2.stdout
  -- with the token check bypassed (internal-only `runInternal` flag): the
  -- compile step's own sorry-warning check independently catches it, since
  -- `sorryAx _ false`'s value literally contains the sorry marker.
  let v2 ← Gate.runInternal p2 "t2" none (some proj) true
  check statsRef (!v2.accepted) "D2 sorryAx rejected even with token check bypassed" v2.reason
  check statsRef (contains v2.reason "axiom:sorryAx" || v2.reason == "sorry_warning")
    "D2 sorryAx caught by axiom-or-sorry-warning check when bypassed" v2.reason

-- D3 statement/prefix tamper (regresses: the gate must not accept a candidate
-- whose statement was weakened, or that smuggled in an extra top-level decl)
def d3 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "gateD3_"
  let refPath := wd / "reference.lean"
  writeFile refPath "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n"
  let p1 := wd / "c1.lean"
  writeFile p1 "theorem t2 (n : Nat) : n + 0 = n := by\n  simp\n"
  let r1 ← runGateCli proj #[p1.toString, "--theorem", "t2", "--reference", refPath.toString, "--project", proj.toString]
  check statsRef (contains r1.stdout "REJECTED: statement_modified") "D3 statement tamper rejected" r1.stdout
  let p2 := wd / "c2.lean"
  writeFile p2 "theorem helper : True := trivial\n\ntheorem t2 (n : Nat) : n + 0 + 0 = n := by\n  omega\n"
  let r2 ← runGateCli proj #[p2.toString, "--theorem", "t2", "--reference", refPath.toString, "--project", proj.toString]
  check statsRef (contains r2.stdout "REJECTED: prefix_modified") "D3 prefix tamper (extra helper) rejected" r2.stdout

-- D4 comment/string desync exploit (rocq-mcp-evolve D4): a `sorry` hidden
-- behind a trailing `-- /-`-style comment trick, or an `#eval "/-"` placed in
-- the proof region, must never be ACCEPTED -- since the gate decides on
-- Lean's own parsed `Syntax`, comments/strings never fool it either way.
def d4 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "gateD4_"
  let p1 := wd / "c1.lean"
  writeFile p1 "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  exact (by\n    skip\n    sorry) -- endcomment /- \n"
  let r1 ← runGateCli proj #[p1.toString, "--theorem", "t2", "--project", proj.toString]
  check statsRef (r1.exitCode == 1) "D4 desync variant 1 (trailing comment) rejected" r1.stdout
  check statsRef (!contains r1.stdout "ACCEPTED") "D4 desync variant 1 never ACCEPTED" r1.stdout
  let p2 := wd / "c2.lean"
  writeFile p2 "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n  #eval \"slash-dash-marker\"\n"
  let r2 ← runGateCli proj #[p2.toString, "--theorem", "t2", "--project", proj.toString]
  check statsRef (r2.exitCode == 1) "D4 desync variant 2 (#eval string) rejected" r2.stdout
  check statsRef (!contains r2.stdout "ACCEPTED") "D4 desync variant 2 never ACCEPTED" r2.stdout

-- D5 native_decide (regresses: the axiom `Lean.ofReduceBool` a "kernel-checked"
-- native_decide close silently pulls in must never be waved through)
def d5 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "gateD5_"
  let p := wd / "c.lean"
  writeFile p "theorem t3 : (2:Nat) + 2 = 4 := by native_decide\n"
  let r ← runGateCli proj #[p.toString, "--theorem", "t3", "--project", proj.toString]
  check statsRef (contains r.stdout "REJECTED: forbidden_token:native_decide") "D5 native_decide forbidden_token" r.stdout
  let v ← Gate.runInternal p "t3" none (some proj) true
  check statsRef (!v.accepted) "D5 native_decide rejected even with token check bypassed" v.reason
  check statsRef (contains v.reason "axiom:Lean.ofReduceBool") "D5 axiom:Lean.ofReduceBool when bypassed" v.reason

-- D6 injected axiom via `run_tac` + `Lean.addDecl (.axiomDecl ..)` (regresses:
-- a metaprogram that fabricates a bogus axiom mid-proof, then discharges the
-- goal from it, must never be accepted -- neither by the token scan nor, if
-- that were bypassed, by the axiom audit)
def d6 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "gateD6_"
  let p := wd / "c.lean"
  writeFile p <| "import Lean\n" ++
    "theorem t4 : (0:Nat) = 1 := by\n" ++
    "  run_tac do\n" ++
    "    Lean.addDecl (Lean.Declaration.axiomDecl\n" ++
    "      { name := `cheat, levelParams := [], type := Lean.mkConst ``False, isUnsafe := false })\n" ++
    "  exact cheat.elim\n"
  let r ← runGateCli proj #[p.toString, "--theorem", "t4", "--project", proj.toString]
  check statsRef (r.exitCode == 1) "D6 injected axiom CLI exit 1"
  check statsRef (contains r.stdout "REJECTED: forbidden_token:") "D6 injected axiom rejected via forbidden token" r.stdout
  let v ← Gate.runInternal p "t4" none (some proj) true
  check statsRef (!v.accepted) "D6 injected axiom rejected even with token check bypassed" v.reason
  check statsRef (v.reason == "axiom:cheat") "D6 axiom:cheat when bypassed" v.reason

-- D7 unchecked smuggle: `run_tac` sets `debug.skipKernelTC` (an ordinary
-- function call, not the `set_option` command -- the only reachable "unchecked
-- add" path that still updates the elaborator-visible environment; a raw
-- `Lean.Kernel.Environment.addDeclWithoutChecking` call does NOT, since it
-- returns a `Kernel.Environment`, a different type with no path back into
-- the live elaborator `Environment` from a tactic -- see Gate.lean's Replay
-- section and the report for this documented finding) then `Lean.addDecl`s an
-- ill-typed "theorem" that only the KERNEL (never the elaborator's type
-- inference, since the value is hand-built `Expr`s) would reject.
-- Regresses: exactly the `addDeclWithoutChecking`-shaped attack the
-- kernel-replay step exists for.
def d7 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "gateD7_"
  let p := wd / "c.lean"
  writeFile p <| "import Lean\n" ++
    "theorem t5 : (0:Nat) = 1 := by\n" ++
    "  run_tac do\n" ++
    "    Lean.withOptions (fun o => Lean.debug.skipKernelTC.set o true) do\n" ++
    "      Lean.addDecl (Lean.Declaration.thmDecl\n" ++
    "        { name := `cheat, levelParams := [], type := Lean.mkConst ``False, value := Lean.mkConst ``True.intro })\n" ++
    "  exact cheat.elim\n"
  let r ← runGateCli proj #[p.toString, "--theorem", "t5", "--project", proj.toString]
  check statsRef (r.exitCode == 1) "D7 unchecked smuggle CLI exit 1"
  check statsRef (contains r.stdout "REJECTED: forbidden_token:") "D7 rejected via forbidden token (run_tac)" r.stdout
  let v ← Gate.runInternal p "t5" none (some proj) true
  check statsRef (!v.accepted) "D7 rejected even with token check bypassed" v.reason
  check statsRef (contains v.reason "kernel_replay_failed:cheat")
    "D7 kernel_replay_failed:cheat when bypassed (kernel type mismatch)" v.reason

-- D8 wrong theorem name / missing target
def d8 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "gateD8_"
  let p := wd / "c.lean"
  writeFile p "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  omega\n"
  let r ← runGateCli proj #[p.toString, "--theorem", "does_not_exist", "--project", proj.toString]
  check statsRef (r.exitCode == 1) "D8 missing target CLI exit 1"
  check statsRef (contains r.stdout "REJECTED: target_missing") "D8 target_missing" r.stdout
  let v ← Gate.run p "does_not_exist" none (some proj)
  check statsRef (!v.accepted && v.reason == "target_missing") "D8 library target_missing" v.reason

-- D9 the one tolerated header addition: a candidate whose ONLY difference
-- from the reference (besides the target's proof) is a literal
-- `import Mathlib.Tactic` line must NOT be rejected by the tamper check --
-- the core project has no Mathlib, so the line is tolerated by the tamper
-- check (no prefix_modified/statement_modified) and it is the *compile* that
-- then fails for lack of Mathlib, proving the two checks are properly
-- separated (see Gate.lean's `checkTamper`/D9 in the report).
def d9 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "gateD9_"
  let refPath := wd / "reference.lean"
  writeFile refPath "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n"
  let p := wd / "c.lean"
  writeFile p "import Mathlib.Tactic\ntheorem t2 (n : Nat) : n + 0 + 0 = n := by\n  omega\n"
  let r ← runGateCli proj #[p.toString, "--theorem", "t2", "--reference", refPath.toString, "--project", proj.toString]
  check statsRef (!contains r.stdout "prefix_modified") "D9 extra import not flagged prefix_modified" r.stdout
  check statsRef (!contains r.stdout "statement_modified") "D9 extra import not flagged statement_modified" r.stdout
  check statsRef (contains r.stdout "REJECTED: compile_error") "D9 rejected by compile, not by tamper" r.stdout

-- D10 reference_unusable (report finding F1): `step4TypeCheck` used to
-- return `none` (accept, i.e. skip the type check entirely) both when the
-- reference failed to compile and when the reference simply lacked a
-- declaration by the requested name in its compiled environment -- and
-- step1's own reference-side `Text.findDecl` miss used to be reported as
-- `target_missing`, indistinguishable from the *candidate's* own missing
-- target. All of these are now `reference_unusable:<detail>`, never a
-- silent pass and never conflated with the candidate's `target_missing`.
def d10 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "gateD10_"
  let candPath := wd / "candidate.lean"
  writeFile candPath "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  omega\n"
  -- D10a: `--reference` points at a file that doesn't exist at all.
  let missingRefPath := wd / "does_not_exist.lean"
  let r1 ← runGateCli proj
    #[candPath.toString, "--theorem", "t2", "--reference", missingRefPath.toString, "--project", proj.toString]
  check statsRef (r1.exitCode == 1) "D10a CLI exit 1"
  check statsRef (contains r1.stdout "REJECTED: reference_unusable:") "D10a CLI reference_unusable" r1.stdout
  let v1 ← Gate.run candPath "t2" (some missingRefPath) (some proj)
  check statsRef (!v1.accepted && contains v1.reason "reference_unusable:")
    "D10a library reference_unusable" v1.reason
  -- D10b: the reference file exists and would compile, but has no
  -- declaration named "t2" at all (a differently-named theorem) -- the
  -- reference is unusable for comparison, a different failure from the
  -- candidate's own target being missing (D8), so it must not be reported
  -- as plain `target_missing`.
  let wrongNameRefPath := wd / "wrong_name_reference.lean"
  writeFile wrongNameRefPath "theorem not_t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n"
  let r2 ← runGateCli proj
    #[candPath.toString, "--theorem", "t2", "--reference", wrongNameRefPath.toString, "--project", proj.toString]
  check statsRef (r2.exitCode == 1) "D10b CLI exit 1"
  check statsRef (contains r2.stdout "REJECTED: reference_unusable:target_missing:t2")
    "D10b CLI reference_unusable:target_missing" r2.stdout
  check statsRef (!contains r2.stdout "REJECTED: target_missing")
    "D10b not conflated with candidate's own target_missing" r2.stdout
  let v2 ← Gate.run candPath "t2" (some wrongNameRefPath) (some proj)
  check statsRef (!v2.accepted && contains v2.reason "reference_unusable:target_missing")
    "D10b library reference_unusable:target_missing" v2.reason

-- D11 target-scoped compile errors / sorry warnings (report finding F2): a
-- task file with OTHER holes (other `sorry` theorems, or an earlier broken
-- proof Lean still admits with an error) used to make the gate reject a
-- correct proof of the TARGET with `sorry_warning`/`compile_error` that
-- properly belonged to some unrelated declaration. Both are now scoped to
-- the target's own line range `[startLine+1, endLine+1]`.
def d11 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "gateD11_"
  -- D11a: multi-hole reference (a sorry, and a genuinely broken proof using
  -- an unknown tactic) -- a correct proof of the target (t2) must still be
  -- ACCEPTED; the other declarations' holes are none of the target's
  -- business.
  let refPath1 := wd / "reference1.lean"
  writeFile refPath1 <|
    "theorem a : True := by\n  sorry\n\n" ++
    "theorem b1 (n : Nat) : n + 1 = 1 + n := by\n  bogus_tac\n\n" ++
    "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n"
  let candPath1 := wd / "candidate1.lean"
  writeFile candPath1 <|
    "theorem a : True := by\n  sorry\n\n" ++
    "theorem b1 (n : Nat) : n + 1 = 1 + n := by\n  bogus_tac\n\n" ++
    "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  omega\n"
  let r1 ← runGateCli proj
    #[candPath1.toString, "--theorem", "t2", "--reference", refPath1.toString, "--project", proj.toString]
  check statsRef (r1.exitCode == 0) "D11a CLI exit 0" s!"{r1.stdout}\n{r1.stderr}"
  check statsRef (contains r1.stdout "ACCEPTED") "D11a multi-hole reference still ACCEPTED" r1.stdout
  -- D11b: soundness backstop -- the target's own proof is clean-looking
  -- (`exact h n`) but leans on a *sorried* earlier declaration (`h`); scoping
  -- the compile-error/sorry-warning check to the target must NOT let this
  -- through, because step 5's `collectAxioms` follows the dependency and
  -- finds `sorryAx` transitively.
  let refPath2 := wd / "reference2.lean"
  writeFile refPath2 <|
    "theorem h (n : Nat) : n + 0 + 0 = n := by\n  sorry\n\n" ++
    "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n"
  let candPath2 := wd / "candidate2.lean"
  writeFile candPath2 <|
    "theorem h (n : Nat) : n + 0 + 0 = n := by\n  sorry\n\n" ++
    "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  exact h n\n"
  let r2 ← runGateCli proj
    #[candPath2.toString, "--theorem", "t2", "--reference", refPath2.toString, "--project", proj.toString]
  check statsRef (r2.exitCode == 1) "D11b CLI exit 1"
  check statsRef (contains r2.stdout "REJECTED: axiom:sorryAx")
    "D11b sorried dependency caught via axiom:sorryAx, not waved through" r2.stdout

-- D12 byte-level tamper check (report finding F3): the old tamper check
-- compared only declaration texts (`Text.findDecls`) and header lines, so a
-- candidate could smuggle in a top-level command that is not itself a
-- declaration -- `set_option`, `variable`, a bare `#eval` -- between/around
-- declarations without tripping `prefix_modified`/`suffix_modified`. The new
-- byte-level before/after comparison catches all of these regardless of
-- what kind of command was inserted.
def d12 (statsRef : IO.Ref Stats) : IO Unit := do
  let proj ← coreProject
  let wd ← tmpdir "gateD12_"
  let refPath := wd / "reference.lean"
  writeFile refPath "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  sorry\n"
  -- an ordinary function-call form (not the `set_option` *command*) would
  -- already be a `forbidden_token` inside the proof (see D7); here it's
  -- smuggled in as its own top-level command, entirely outside the target's
  -- proof syntax, which the old decl-only tamper check never looked at.
  let p1 := wd / "c_setoption.lean"
  writeFile p1 <|
    "set_option debug.skipKernelTC true\n" ++
    "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  omega\n"
  let r1 ← runGateCli proj #[p1.toString, "--theorem", "t2", "--reference", refPath.toString, "--project", proj.toString]
  check statsRef (contains r1.stdout "REJECTED: prefix_modified")
    "D12 set_option command before target rejected prefix_modified" r1.stdout
  let p2 := wd / "c_eval_after.lean"
  writeFile p2 <|
    "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  omega\n\n" ++
    "#eval IO.println \"x\"\n"
  let r2 ← runGateCli proj #[p2.toString, "--theorem", "t2", "--reference", refPath.toString, "--project", proj.toString]
  check statsRef (contains r2.stdout "REJECTED: suffix_modified")
    "D12 #eval command after target rejected suffix_modified" r2.stdout
  let p3 := wd / "c_variable.lean"
  writeFile p3 <|
    "variable (h : False)\n" ++
    "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  omega\n"
  let r3 ← runGateCli proj #[p3.toString, "--theorem", "t2", "--reference", refPath.toString, "--project", proj.toString]
  check statsRef (contains r3.stdout "REJECTED: prefix_modified")
    "D12 variable command before target rejected prefix_modified" r3.stdout
  -- regression: D1's legit accept and D9's one tolerated header addition
  -- must still work under the new byte-level check (exercised again here,
  -- directly against the same reference, for locality with the rest of D12).
  let candOk := wd / "c_ok.lean"
  writeFile candOk "theorem t2 (n : Nat) : n + 0 + 0 = n := by\n  omega\n"
  let rOk ← runGateCli proj #[candOk.toString, "--theorem", "t2", "--reference", refPath.toString, "--project", proj.toString]
  check statsRef (contains rOk.stdout "ACCEPTED") "D12 unmodified candidate still ACCEPTED" rOk.stdout
  let candMathlib := wd / "c_mathlib_header.lean"
  writeFile candMathlib "import Mathlib.Tactic\ntheorem t2 (n : Nat) : n + 0 + 0 = n := by\n  omega\n"
  let rMathlib ← runGateCli proj
    #[candMathlib.toString, "--theorem", "t2", "--reference", refPath.toString, "--project", proj.toString]
  check statsRef (!contains rMathlib.stdout "prefix_modified")
    "D12 tolerated import Mathlib.Tactic still not flagged prefix_modified" rMathlib.stdout

def run (statsRef : IO.Ref Stats) : IO Unit := do
  runCase statsRef "D1" d1
  runCase statsRef "D2" d2
  runCase statsRef "D3" d3
  runCase statsRef "D4" d4
  runCase statsRef "D5" d5
  runCase statsRef "D6" d6
  runCase statsRef "D7" d7
  runCase statsRef "D8" d8
  runCase statsRef "D9" d9
  runCase statsRef "D10" d10
  runCase statsRef "D11" d11
  runCase statsRef "D12" d12

end Tests.Gate
