# Test suite architecture (Lean, integration-level)

Philosophy (inherited from rocq-mcp-evolve, and from this project's own
Python prototype): every integration test exercises the REAL server
end-to-end (spawn the built `lean-mcp-evolve` binary via `lake env` → MCP
stdio → assert on behaviour) and encodes either a core contract or a
regression for a bug the Rocq experiment actually found (each case cites its
origin in a comment). One exception: the pure text layer (`LeanMcpEvolve.Text`)
has unit tests with no server involved, because the Rocq API audit found the
"where is it in the text" layer to be the bug nest (comment/string desync,
keyword regexes matching inside comments) — here it is parser-driven instead
of regex-driven, but the same property (comment/string safety, correct
extents) still needs direct checking.

```
Tests/
  Helpers.lean    mini-lib: spawn the server, JSON-RPC round trips, the core/Mathlib project factories, TAP-ish reporting, repoRoot
  Fixtures/       F1 (Mathlib real-arith), F2 (Nat, core), F3 (∧ goal, core), Build.lean (5 declarations, 3 broken)
  Text.lean       suite T: LeanMcpEvolve.Text unit checks (12 cases, 35 checks)
  Session.lean    suite A: session-server contracts on a core-only project (23 cases, 113 checks)
  Gate.lean       suite D: the out-of-process correctness gate, `lake exe gate` (12 cases D1-D12, 49 checks)
  Mathlib.lean    suite M: Mathlib-backed contracts (5 cases, 29 checks; skipped without a project)
  Main.lean       `lake exe tests [T|A|D|M]` entry point
  ARCHITECTURE.md this file
```

Run everything: `lake exe tests` (after `lake build`). Run one suite:
`lake exe tests T` / `A` / `D` / `M`. T, A and D all run by default (no
project beyond this repo's own core fixture needed). Suite M needs
`LEAN_MCP_TEST_MATHLIB_PROJECT=<built project depending on Mathlib>` and is
run manually, not in CI (see `.github/workflows/ci.yml`) — it needs a
project with Mathlib already built, which takes tens of minutes on its own.

Suite D differs from A in *how* it exercises the system under test: most D
cases invoke the built `gate` executable as a real subprocess (`lake env
<abs .lake/build/bin/gate> ...`, run from the core project directory so
`LEAN_PATH` resolves as it would for a genuine invocation) and assert on its
`ACCEPTED`/`REJECTED: <reason>` stdout line and exit code — mirroring how a
real harness would invoke it. Several cases additionally call the library
API `LeanMcpEvolve.Gate.run`/`runInternal` directly, in-process, to prove
"defense in depth": `runInternal` has a test-only flag to disable the
forbidden-token check (step 2) so the case can show that steps 3–6
independently reject what step 2 would already have caught.

## Helpers.lean contract

- `coreProject` — builds (once per test-executable run, cached in a ref) a
  dependency-free Lake project under a fresh temp dir, with its own
  `lean-toolchain` copied from this repo's (the server can only load
  `.olean`s built by its own Lean version), `Coreproj/Basic.lean` (a `helper`
  lemma), and runs `lake build` on it. Fixtures for suite A are written INTO
  it under fresh unique names (`freshSuffix`) so the server's own
  project-load-path discovery (`lake env printenv LEAN_PATH`) resolves them.
- `mathlibProject` — `some <path>` iff `LEAN_MCP_TEST_MATHLIB_PROJECT` is set
  and `.lake/packages/mathlib` exists under it, else `none` (suite M skips).
- `spawnServer cwd envAdds` — spawns the built binary as `lake env <bin>` in
  `cwd`, with `envAdds` layered onto the inherited environment; stderr is
  drained in the background so a chatty child (`LEAN_MCP_DEBUG=1`) never
  blocks on a full pipe. `Server.rpc`/`initialize`/`tools`/`call` send one
  JSON-RPC line and block for the matching response by `id`; `Server.close`
  closes stdin and waits briefly before killing the child.
- `fixture name`, `writeFile`, `readFile`, `tmpdir` — small filesystem
  helpers mirroring the Python prototype's `helpers.py` of the same names.
- `check statsRef cond name actual?` — records one TAP-ish `ok - <name>` /
  `FAIL - <name>` line (with the actual value, truncated, printed alongside
  a failure) into a shared `Stats` ref.

## Suite T — text layer (`Tests/Text.lean`), pure, no server, 12 cases / 35 checks

- **T1** `findDecls`/`findDecl`: names and extents of a file mixing a plain
  `theorem`, a doc-commented + attributed one, a `set_option … in` one, an
  `example`, a pattern-style declaration and a trailing one — start/end
  lines fold in the doc comment/attribute/`set_option` prefix; lookup of a
  name that doesn't exist returns `none`.
- **T2** declaration style classification: `:= by` (`.by`), a bare term
  (`.term`), equation/pattern style (`.pattern`), and a declaration whose
  statement text keeps a *commented-out* `:= by` untouched (comment-aware).
- **T3** default-argument statement rendering ends with `:= by` even when
  the source declaration had default arguments in its binder.
- **T4** `splitUnits` on a script mixing plain tactics, an `induction …
  with | zero => … | succ …` block (one unit), a `·`-bullet block spanning
  multiple lines (one unit), a bracket-continued bullet, and a
  continuation line — six units total, split by the tactic-sequence parser
  rather than indentation.
- **T5** `splitUnits` edge cases: a leading `by`, a `;`-joined one-liner
  kept as one unit, and blank input producing zero units.
- **T6** `indentBlock` reindents a mixed single-/multi-line tactic array.
- **T7** `stripComments` preserves the codepoint length of the source (so
  line numbers survive), keeps a string literal that looks like a comment
  untouched, and removes nested `/- … -/` block-comment markers.
- **T8**/**T9** `scanForbidden`: hits inside comments/strings are ignored
  (T8, alongside a real `native_decide` hit further down), and the Rocq D4
  desync exploit — a forbidden token straddling a comment/string boundary —
  is still caught correctly (T9 regression).
- **T10** `parseTryThis`: extracts the suggested tactic from a
  `Try this:\n  [apply] exact …` bracket-tagged message and from a
  single-line `Try this: simp only […]` message; returns `none` for
  unrelated text.
- **T11** `importsOf`/`headerEnd`: the import list of a one-import file, the
  header's end position, and that scanning stops at the first non-import,
  non-comment line.
- **T12** `truncate` keeps head and tail with an "elided" marker in the
  middle for over-length text.

## Suite A — session core (`Tests/Session.lean`), core-only project, 23 cases / 113 checks

Env for all unless stated: `LEAN_ENV_V2=1`, `LEAN_TASK_FILE=<fixture copy>`,
`LEAN_WORKDIR=<tmpdir>`, `LEAN_ENABLE_TOOLS` as needed. Every case spawns a
*fresh* server (sessions are single-task) and closes it when done.

- **A0** tool surface: exactly the nine tools with no `LEAN_ENABLE_TOOLS`
  set; `LEAN_ENABLE_TOOLS=step,state` trims to just those two.
- **A1** commit-good-prefix (Rocq A1): a real tactic followed by
  `bogus_tac` commits 1 and reports ERROR at `bogus_tac`; a subsequent
  multi-line `induction … with` completes the proof; `candidate.lean`
  contains the file prefix exactly once and no `sorry`.
- **A2** auto-Qed handshake (atlas fix 1): a single closing tactic alone
  completes the proof with no explicit closer, echoing the finished
  declaration.
- **A3** `try` semantics (Rocq A3): candidates are evaluated independently
  from the same state; the FIRST whose tactics all pass is committed even
  with goals left, later fully-successful candidates are reported "(not
  committed)"; a second `try` call against the new state commits and
  completes.
- **A3b** `try` with `commit: "none"`: three closers all report OK, closes
  ALL goals, but nothing is committed.
- **A4**/**A4b** `auto_close` progress rule (A22 false-winner): an honest
  miss writes no `candidate.lean`; a real closure is COMMITTED, completes
  the proof, and writes `candidate.lean`; a plain core arithmetic goal also
  closes.
- **A6** rollback + query non-commit (Rocq A6): `#check` executes and its
  output is shown but it is never committed; rollback restores the prior
  goal count; `candidate.lean` never contains a `#check` line.
- **A7** forbidden placeholders (env-v2 `Require` analogue): `sorry`, and
  under `LEAN_ENV_V2=1` `native_decide`, are refused up front with nothing
  committed and the state unaffected.
- **A8** error enrichment (Rocq A8): a Rocq-ism (`intros n.`) and `rewrite`
  each get a hint mentioning the period/Rocq or `rw [h]`; a typo'd lemma
  name gets near-miss suggestions including `Nat.add_zero`; a tool name
  typed as a tactic is caught too.
- **A9** `check` (A24): failure leaves the valid prefix committed with the
  repair phrasing ("you are now AT that point in the proof — repair from
  here … or rollback and resubmit"); a subsequent fresh `check` discards
  the prior partial work and can still complete.
- **A12** runtime `open` (A29): the pre-open guard directs to `open`; a
  missing file errors; the default target is the first unproven
  declaration; a named theorem is targeted directly; a missing theorem name
  errors; the named theorem is provable via `rfl`; the written candidate
  leaves other declarations untouched and only replaces the target's proof.
- **A14** `build` + reach-any-theorem (A33/A36): a 5-declaration fixture
  with 3 broken ones reports "2 declaration(s) OK, 3 hole(s)" in one call
  (an error, a `sorry`, and a false `decide` refutation all listed); opening
  a theorem *after* a broken one succeeds (with a note about the earlier
  declaration); it is provable via `omega`; `build` is pure — the live
  session is unaffected and still on its own target after calling it.
- **A15** `verify`: reports either a clean build or lists forbidden `sorry`
  left behind by other tests' fixtures (both are acceptable — the test
  doesn't control what other fixtures leave in the shared core project).
- **A16** timeout safety: a slow `decide` under `LEAN_STEP_TIMEOUT=2`
  reports TIMEOUT (or Lean's own heartbeat error) with nothing committed,
  and the session is still usable afterwards.
- **A17** search tactics: `exact?` is committed as the concrete tactic it
  finds, not literally as `exact?`; the response reports what was found.
- **A18** already-complete guard on every mutating tool (`step`, `try`,
  `auto_close`, `check`); `state` shows COMPLETE; `rollback` still works
  when complete and reopens the goal.
- **A19** structured units: a `constructor` followed by two `·`-bullets
  commits as 3 tactics (not 1 blob), completing the proof with bullet text
  preserved in the committed script.
- **A20** JSONL instrumentation: an `initialize` record and a `tool_call`
  record (for `step`) both appear in `LEAN_LOG_FILE`, merged with
  `LEAN_LOG_META` (a `run` field survives), with a `complete` field set
  correctly.
- **A21** axiom injection in-session: text-level scanning and the kernel
  check alone don't catch a custom axiom smuggled in via `run_tac` +
  `Lean.addDecl (.axiomDecl ..)` (adding an axiom is always kernel-valid),
  so `Driver.completionCheck`'s fail-closed axiom-allowlist audit is the
  actual backstop — never `PROOF COMPLETE`, nothing committed, no
  `candidate.lean`; run both with and without `LEAN_ENV_V2` (under ENV_V2
  the up-front `run_tac`/`addDecl` refusal already blocks it, so this also
  checks the axiom-audit path still holds without that refusal).
- **A22** `native_decide` refused ALWAYS, not just under `LEAN_ENV_V2`: a
  proof that trusts the compiler is not a proof for this server's purposes
  regardless of mode.
- **A23** `example` completion: the target constant elaborates anonymously
  (no name to relocate in the environment for the axiom audit), so
  `completionCheck` must re-elaborate it under a synthetic `theorem` name
  instead of best-effort-passing when the lookup comes back empty (the old,
  unsafe fallback) — `simp` still reaches `PROOF COMPLETE` and
  `candidate.lean` holds the example with its proof replaced.
- **A24** `sorryAx` spelled directly (`exact (sorryAx _ false)`), bypassing
  the plain `sorry` keyword `rejectForbidden` already refuses up front:
  still refused/never yields `PROOF COMPLETE`, nothing committed, no
  `candidate.lean` — caught either by the up-front `alwaysForbidden` scan or,
  if that were bypassed, by `completionCheck`'s axiom audit.

## Suite D — correctness gate (`Tests/Gate.lean`), 12 cases D1–D12 / 49 checks

The Lean analogue of rocq-mcp-evolve's `harness/gate.py` tests — see
`docs/DESIGN.md` §3b for the Rocq → Lean step mapping. Every case writes a
reference/candidate pair (or just a candidate) into a fresh temp directory
and drives the built `gate` executable (`lake exe gate`); several also call
the library API directly in-process for "defense in depth" (see above).

- **D1** legit accept: regresses that a genuine closer must still pass
  *every* gate step — tamper/token/compile/type/axiom/kernel-replay — not
  just the in-session check; also asserts the accepted verdict's axioms are
  all within the standard set.
- **D2** placeholders (`sorry`, `sorryAx`): regresses that an
  in-session-looking "success" that is really a give-up must still be
  rejected, both by the token scan and, with that bypassed, independently by
  the compile step's own sorry-warning check (`sorryAx _ false`'s value
  literally contains the sorry marker).
- **D3** statement/prefix tamper: regresses that the gate must not accept a
  candidate whose statement was weakened (`statement_modified`) or that
  smuggled in an extra top-level declaration (`prefix_modified`).
- **D4** the Rocq D4 comment/string desync exploit: a `sorry` hidden behind
  a trailing `-- /-`-style comment trick, and an `#eval "..."` placed in the
  proof region, must never be `ACCEPTED` — since the gate decides on Lean's
  own parsed `Syntax`, comments/strings never fool it either way.
- **D5** `native_decide`: regresses that the axiom `Lean.ofReduceBool` a
  "kernel-checked" `native_decide` close silently pulls in must never be
  waved through, caught by the token scan and, if bypassed, by the axiom
  check (`axiom:Lean.ofReduceBool`).
- **D6** injected axiom via `run_tac` + `Lean.addDecl (.axiomDecl ..)`:
  regresses that a metaprogram fabricating a bogus axiom mid-proof, then
  discharging the goal from it, must never be accepted — neither by the
  token scan nor, if bypassed, by the axiom audit (`axiom:cheat`).
- **D7** unchecked smuggle: `run_tac` sets `debug.skipKernelTC` (an ordinary
  function call, not the `set_option` command) then `Lean.addDecl`s an
  ill-typed "theorem" built from hand-constructed `Expr`s that only the
  KERNEL (never the elaborator's type inference) would reject; regresses
  exactly the `addDeclWithoutChecking`-shaped attack the kernel-replay step
  exists for — caught by the token scan and, if bypassed, only by kernel
  replay (`kernel_replay_failed:cheat`).
- **D8** wrong theorem name / missing target: both the CLI and the library
  API report `target_missing` and exit non-zero.
- **D9** the one tolerated header addition: a candidate whose only
  difference from the reference (besides the target's proof) is a literal
  `import Mathlib.Tactic` line must NOT be rejected by the tamper check on a
  project without Mathlib — the tamper check tolerates the line and it is
  the *compile* step that then fails for lack of Mathlib, proving the two
  checks are properly separated (see `Gate.lean`'s `blankMathlibImportLine`
  doc comment and the README's residual-risks list).
- **D10** `reference_unusable` (report finding F1): `step4TypeCheck` used to
  return `none` (accept, i.e. silently skip the type check) when the
  reference failed to compile or lacked the target in its compiled
  environment, and step1's own reference-side lookup miss was reported as
  the misleading `target_missing` (indistinguishable from the *candidate's*
  own missing target, D8). D10a: `--reference` pointing at a nonexistent
  file → `reference_unusable:not_found:<path>`. D10b: a reference file that
  compiles but declares a differently-named theorem, not the requested
  target → `reference_unusable:target_missing:<name>`, and asserts this is
  never conflated with plain `target_missing`.
- **D11** target-scoped compile errors/sorry warnings (report finding F2): a
  task file with other holes must not make a correct proof of the *target*
  fail. D11a: a reference/candidate pair where an unrelated theorem is
  `sorry`-stubbed and another has a genuinely broken proof (unknown tactic)
  — a correct `omega` proof of the target must still be `ACCEPTED`, since
  neither hole's message lands inside the target's own line range. D11b: the
  soundness backstop — the target's proof text looks clean (`exact h n`) but
  depends on a *sorried* earlier declaration `h`; scoping the compile-error
  check to the target does not let this through, because step 5's
  `collectAxioms` follows the dependency and still finds `sorryAx`
  transitively (`REJECTED: axiom:sorryAx`).
- **D12** byte-level tamper check (report finding F3): the previous tamper
  check compared only declaration texts (`Text.findDecls`) and header lines,
  so a candidate could smuggle in a top-level command that is *not itself a
  declaration* between/around declarations without tripping anything. Three
  variants, all against the same reference as D1/D9: `set_option
  debug.skipKernelTC true` inserted before the target → `prefix_modified`;
  `variable (h : False)` inserted before the target → `prefix_modified`;
  `#eval IO.println "x"` appended after the target → `suffix_modified`.
  Also re-asserts, directly alongside these, that an unmodified candidate
  (D1) and the one tolerated `import Mathlib.Tactic` addition (D9) still
  pass under the new byte-level check.

## Suite M — Mathlib-backed (`Tests/Mathlib.lean`), 5 cases / 29 checks

Fixtures are written into a scratch subdirectory of the Mathlib project
(`LeanMcpEvolveTests/`), removed when the suite finishes.

- **M1** hint synthesis (rung 9b): `auto_close` with `LEAN_AUTO_SEARCH=0`
  closes the `(x^6+1)/2 ≥ x^3` goal (fixture F1) with a synthesized
  `nlinarith [sq_nonneg (x ^ 3 - 1), …]`, and `candidate.lean` contains it.
- **M2** Rocq-isms at a real Mathlib goal: `nra` reports a SYNTAX ERROR
  whose hint mentions `nlinarith`; `apply Rmult_le_pos` gets a "Rocq/Coq
  lemma name" hint; a `try` across `nlinarith`/`positivity`/a helper-`have`
  candidate reports the first's error, lists candidate `[3]`, commits a
  working one, and completes.
- **M3** preloading + import echo (A11/A59): a file importing only
  `Mathlib.Data.Real.Basic` gets `import Mathlib.Tactic` injected for the
  session; `linarith` then completes the proof, the response's import echo
  names `linarith` and shows the import line, and `candidate.lean` carries
  both the original and injected imports; with `LEAN_PRELOAD=0` `linarith`
  is `unknown tactic` and `auto_close` either finds a real closer or
  reports an honest miss without even trying the unavailable one.
- **M4** `exact?` inside a `·`-bullet (`constructor\n· omega\n· exact?`)
  completes the proof, and the committed/candidate script carries the found
  tactic rather than the literal `exact?`.
- **M5** `build` on a 3-declaration Mathlib file reports "1 declaration(s)
  OK, 2 hole(s)" (a bad `nra` tactic and a `sorry`); opening the `sorry`
  hole and running `positivity` completes it.

## Non-goals

No mocking, no network, no coverage of a benchmark harness. Any single
suite taking more than a few minutes warm (M aside, which is inherently
Mathlib-slow) is a bug.
