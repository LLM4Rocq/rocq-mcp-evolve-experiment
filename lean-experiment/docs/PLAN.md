# lean-mcp-evolve — implementation plan (Lean-native server)

Status: this is the working spec for the port. The product is a Lean 4
program (a Lake package with one executable, `lean-mcp-evolve`) that speaks
MCP over stdio and drives the Lean prover **in-process**, exactly as
rocq-mcp-evolve drives Rocq in-process. It must rely on existing Lean
constructs wherever one exists (see §3) rather than re-implementing them.

The Python prototype in `prototype-python/` is the **behavioural reference**:
its `tests/test_session.py` / `tests/test_mathlib.py` encode the required
observable behaviour (response phrasings, tool semantics), and
`src/lean_mcp_evolve/session_server.py` + `hints.py` hold the exact message
texts, the hint table, the portfolio and the synthesis rules to port. It is
deleted once the Lean tests pass.

## 1. Hard constraints

- **Tool set = exactly** `open, build, verify, check, step, try, auto_close,
  rollback, state` (rocq-mcp-evolve's default-on set). Nothing added, nothing
  removed. `LEAN_ENABLE_TOOLS` may trim the exposed subset.
- Written in Lean 4. No Python, no shell wrappers in the product.
- Toolchain: `leanprover/lean4:v4.27.0-rc1` (matches the local Mathlib
  project used for suite M, `/Users/jviennot/Documents/Cours/LEAN_2026`).
  The server can only load `.olean`s built by the same Lean version — this
  is inherent to any in-process Lean tool (the REPL, Pantograph, LeanDojo all
  share it). Users build the server with the toolchain of their project.
- Dependency: `leanprover-community/repl` as a Lake `require`, pinned to the
  git tag equal to the toolchain (`v4.27.0-rc1` exists; a clone is at
  `/private/tmp/claude-1981585666/-Users-jviennot-Documents-These-lean-mcp-evolve/a6c821b1-a117-417f-a41d-0db55d749d17/scratchpad/replsrc`
  for reading). It exposes `lean_lib REPL` — import `REPL.Snapshots`,
  `REPL.Frontend`, `REPL.Main` (the last defines the `M` monad, `sorries`,
  `getProofStatus`; import it only if it does not pull in the executable's
  `main`, otherwise copy the 2–3 needed functions with attribution).

## 2. Architecture (one Lake package)

```
lakefile.toml            package lean-mcp-evolve; require repl @ v4.27.0-rc1; lean_lib LeanMcpEvolve; lean_exe lean-mcp-evolve (root LeanMcpEvolve.Main, supportInterpreter = true); lean_exe tests (root Tests.Main)
lean-toolchain           leanprover/lean4:v4.27.0-rc1
LeanMcpEvolve/
  Mcp.lean               MCP stdio server: newline-delimited JSON-RPC 2.0, tool registry, JSONL instrumentation (rocq mcp_core)
  Proc.lean              spawn a process with a hard timeout, capture combined output, kill on timeout (rocq proc.ml)
  Text.lean              declaration location via Lean's PARSER (not regexes), statement/proof split on the syntax tree, tactic-unit splitting via the tactic-sequence parser, candidate assembly
  Driver.lean            session engine on REPL snapshots: prefix processing, proof snapshot from `sorry`, run units with timeout+heartbeats, error classification, goal rendering, completion (kernel) check, whole-file diagnosis, tactic availability, fuzzy names
  Hints.lean             error-hint table (Rocq/Coq-isms, Lean 3-isms, message-keyed), did-you-mean ranking, hint-term synthesis for nlinarith/positivity
  Verify.lean            `lake build` + axiom audit (collectAxioms) + forbidden-token scan
  Session.lean           the nine tools (handlers + schemas + response texts)
  Main.lean              `main`: parse LEAN_ENABLE_TOOLS, run the MCP loop
Tests/
  Main.lean              test executable: spawns the built server over stdio, TAP-ish checks (suites A, M); pure-Lean unit checks for Text (suite T)
  Fixtures/              F1.lean, F2.lean, F3.lean, Build.lean (copy from prototype-python/tests/fixtures)
docs/DESIGN.md, docs/PLAN.md, README.md, tests/ARCHITECTURE.md
```

## 3. Existing Lean constructs to use (and what NOT to hand-roll)

| need | use |
|---|---|
| JSON | `Lean.Json`, `Lean.FromJson`/`ToJson` (derive), `Json.compress`, `Json.parse` |
| JSON-RPC 2.0 messages | `Lean.JsonRpc.Message` / `Request` / `Response` / `RequestError` (`Lean.Data.JsonRpc`) — transport is newline-delimited (MCP stdio), so read `IO.getStdin.getLine` + `Json.parse` + `fromJson? Message`; write `(toJson msg).compress ++ "\n"`. Do not use `readLspMessage` (Content-Length framing). |
| stdio | `IO.getStdin`, `IO.getStdout`, `IO.FS.Stream.putStr`/`flush` |
| processing a file prefix / commands | `REPL.Frontend.IO.processInput` (wraps `Lean.Elab.IO.processCommands` + `processHeader`), producing `Command.State` + messages + info trees |
| search path / imports | `Lean.initSearchPath (← Lean.findSysroot)`; when `LEAN_PATH` is unset and the opened file has a lakefile ancestor, run `lake env printenv LEAN_PATH` in that root (via `Proc`) and `Lean.searchPathRef.modify` — this is the "project load-path auto-discovery" of the Rocq server |
| proof states | `REPL.ProofSnapshot` (`create`, `runString`, `runTacticM`, `ppGoals`, `pickle`); obtained from a `sorry` via the info tree (`REPL.Main.sorries` / `TacticInfo` nodes) — study `REPL/Main.lean` `runCommand` + `runProofStep` and `createProofStepReponse`/`getProofStatus` |
| goal pretty-printing | `ProofSnapshot.ppGoals` (`Lean.Meta.ppGoal`) — render as `goals: N` + goals separated by blank lines (same as the prototype) |
| tactic parsing | `Lean.Parser.runParserCategory env \`tactic src` for availability and error kind; for unit splitting parse the agent text as a tactic sequence (`Lean.Parser.Tactic.tacticSeq` / category `tactic` with `sepByIndent`) and take each top-level tactic's `Syntax` source range — parser-driven, no indentation heuristics |
| declaration location | parse the file with `Lean.Parser.parseHeader` + `Lean.Parser.parseCommand` loop (no elaboration): a `Lean.Parser.Command.declaration` node gives kind, `declId` name (qualified with the enclosing `namespace`s tracked from `namespace`/`section`/`end` commands), start/end positions (`Syntax.getPos?`/`getTailPos?` with `String.Pos` → line via `FileMap`), and the `declVal` child (`declValSimple` `:= term`, `declValEqns` pattern matching, `whereStructInst`). Attributes/doc comments/`set_option … in` belong to the same command syntax |
| timeouts / hang safety | run each tactic in `IO.asTask` and wait with a wall-clock budget; cancel with `IO.CancelToken` placed in `Core.Context.cancelTk?` (tactics check it in `Core.checkSystem`) and cap `maxHeartbeats` in `Core.Context` — the allocation-driven interruption is Lean's own heartbeat mechanism (analogue of memprof-limits) |
| completion ("Qed") | (1) goals empty; (2) `REPL`'s `getProofStatus` = `"Completed"` (kernel type-checks the proof term); (3) re-elaborate the finished declaration text as a command in the prefix state: zero error messages, no `declaration uses 'sorry'` — the same gate the harness applies |
| forbidden placeholders | `Lean.collectAxioms` on the elaborated declaration: reject `sorryAx`, `Lean.ofReduceBool`, and (under `LEAN_ENV_V2=1`) any axiom outside `propext`, `Classical.choice`, `Quot.sound`; plus the up-front text refusal of `sorry`/`admit` in agent tactics (a proof that gives up cannot help) |
| did-you-mean | `Lean.FuzzyMatching.fuzzyMatchScoreWithThreshold?` (what the language server's completion uses) over `env.constants` short names, ranked as in the prototype (typo-closeness + shared fragments + same namespace) |
| `lake build` | `IO.Process.spawn` with piped output, wait in a task with a deadline, `kill` on timeout (Proc.lean); serialise with a lock file |
| instrumentation | one JSON line per tool call appended to `LEAN_LOG_FILE`, merged with `LEAN_LOG_META` (`IO.FS.Handle.mk … .append`) |

## 4. Session model (Driver)

```
structure Session where
  file        : System.FilePath
  name        : Name                 -- target declaration
  prefixState : Command.State        -- environment after the file prefix (+ preload)
  prefixText  : String               -- file text up to (not incl.) the declaration
  stmtText    : String               -- the statement, normalised to end with `:= by`
  tail        : String               -- rest of the file after the original declaration
  indent      : String               -- tactic indentation for the finished script
  base        : ProofSnapshot        -- goal state right after `:= by`
  committed   : List (String × ProofSnapshot)  -- newest first, immutable snapshots (O(1) rollback)
  complete    : Bool
  preloaded   : Option String        -- injected `import Mathlib.Tactic` line, if any
```

- **open{file, theorem?}**: read file; discover project + search path; parse
  to locate declarations; target = named theorem (exact qualified name, then
  as-written, then unique suffix) or, by default, the first declaration whose
  elaboration (whole-file `processInput`) reports an error or `sorry`. Process
  the prefix text (everything before the declaration; earlier broken proofs
  are admitted by Lean's error recovery — note their count). Elaborate
  `stmtText ++ " sorry"` in the prefix state, collect the sorry's
  `ProofSnapshot` → `base`. Preload: if the project has Mathlib
  (`.lake/packages/mathlib` under the root) and the file imports neither
  `Mathlib` nor `Mathlib.Tactic`, add `import Mathlib.Tactic` after the import
  block (`LEAN_PRELOAD=0` disables; if the import fails, retry without).
  Response: `opened <file> — proving <name>.` + goals block (+ notes).
  Statement errors → error result "its statement fails to elaborate: …".
- **step{text}**: refuse `sorry`/`admit` (and under ENV_V2 `native_decide`,
  `set_option`, `axiom`, `import`) up front. Split into units with the
  parser; `#`-prefixed lines are queries: run as commands in the prefix
  state (with the committed proof? not needed — the prefix state), report
  their messages, never committed. Run units in order from the current
  snapshot with `LEAN_STEP_TIMEOUT` (default 30 s) each; each success is
  appended to `committed`; first failure stops: report
  `<k> tactic(s) committed, then ERROR at \`<unit>\`:\n<msg>\n\nstate unchanged since last success:\n<goals>`
  (+ `hint:` / `near-miss names that DO exist:` lines). Timeouts:
  `… then TIMEOUT (>Ns) at \`<unit>\` — this tactic is too slow here; try something else. (interrupted work cancelled)`.
  Search tactics (`exact?`, `apply?`, `rw?`, `simp?`, …) are committed as the
  tactic they suggest (parse the `Try this:` info message; splice at the
  message's position inside the unit).
  When goals are empty after a unit → completion check → `PROOF COMPLETE.
  The finished declaration (replace the theorem's proof in your file with this):\n<stmt>\n<indented script>` (+ import echo) and write
  `LEAN_WORKDIR/candidate.lean` = prefix + finished declaration + tail.
- **try{candidates, commit?}**: ≤ 8 candidates, each evaluated from the same
  snapshot (immutable snapshots make this trivially independent); the first
  whose units ALL pass is committed (`<< COMMITTED`), others
  `(not committed)`; per-candidate lines exactly as the prototype's
  `_try_line` (`OK, closes ALL goals` / `OK, N goal(s) left; next: <concl>` /
  `error at …` / `syntax error at …` / `timeout (>Ns) at …`), then
  `after commit:` + goals, or `nothing committed; state unchanged.`, or the
  completion message.
- **auto_close{}**: portfolio (rfl, trivial, simp, omega, decide, norm_num,
  linarith, nlinarith, positivity, ring, `field_simp`+`ring`, simp_all, aesop,
  tauto, bound, gcongr, `norm_num [*]`, `intros`+linarith, `intros`+nlinarith)
  filtered by availability (does it parse in this env?), then synthesized
  `nlinarith [...]`/`positivity` candidates from the first goal (variables of
  type ℝ/ℚ/ℤ/ℕ from the local context — use the `MetaM` context, not the
  printed string; `0 < a`/`0 ≤ a` hypotheses → `mul_pos h1 h2`; even powers in
  the conclusion `x ^ 6` → `sq_nonneg (x ^ 3 - 1)`, `sq_nonneg (x ^ 3 + 1)`),
  then `exact?` last (`LEAN_AUTO_SEARCH=0` disables). Budget
  `LEAN_AUTO_TIMEOUT` 6 s per closer (double for synthesized ones,
  `LEAN_SEARCH_TIMEOUT` 25 s for `exact?`). Progress rule: a winner must
  close the proof or reduce the goal count. Responses:
  `\`<closer>\` closes it — COMMITTED.` + completion, or
  `\`<closer>\` closes the current goal — COMMITTED.` + goals, or
  `no finisher applies (tried N: <first words>). Do structural work (intro / rcases / have a helper fact) and try again.`
- **check{script}**: fresh attempt from `base` (committed cleared; say
  `(fresh attempt: N previously committed tactic(s) discarded)`), then as
  step but with the repair phrasing `you are now AT that point in the proof — repair from here (step/try/auto_close) or rollback and resubmit:`.
- **rollback{count}**: drop `count` (default 1) snapshots →
  `rolled back N tactic(s). M remain committed.` + goals.
- **state{}**: `proving <name> in <file>\ncommitted proof:\n<script or (nothing committed yet)>\n[PROOF COMPLETE.\n]` + goals.
- **build{file}**: whole-file `processInput`; group messages by declaration
  range; error → `- <name>: fails at \`<line text>\` (line N): <msg>`; sorry →
  `- <name>: uses \`sorry\`: the file compiles but this statement is not proved`;
  `BUILD OK: N declaration(s), no holes.` / `BUILD: N declaration(s) OK, M hole(s):` … `Fix a hole with open{file, theorem:<name>} then prove it.`
  Pure: never touches the session.
- **verify{}**: root = `LEAN_PROJECT_ROOT` > opened file's project > cwd.
  `lake build` (timeout `LEAN_BUILD_TIMEOUT` 600 s, lock file), then the
  axiom audit of the project's modules (import them; for every constant
  declared in them `collectAxioms`; flag `sorryAx`/`Lean.ofReduceBool`/
  non-standard axioms) and a forbidden-token scan of `.lean` files (`sorry`,
  `admit`, `axiom`, `native_decide`; comment/string-aware). `VERIFY OK: build clean, no forbidden placeholders. Safe to declare the project done.` or `VERIFY FAILED — fix before finishing:` + `- …` lines.
- Already-complete guard on step/try/auto_close/check:
  `The proof is already COMPLETE. Reply DONE — do not call more tools.`
- Pre-open guard: `no proof is open — call the \`open\` tool with the path of a .lean file first` (unless `LEAN_TASK_FILE` presets a file, opened lazily).

## 5. Environment variables (unchanged from the prototype)

`LEAN_ENABLE_TOOLS`, `LEAN_HINTS`, `LEAN_SUGGEST`, `LEAN_AUTO2`, `LEAN_PRELOAD`,
`LEAN_IMPORT_ECHO`, `LEAN_AUTO_SEARCH`, `LEAN_STEP_TIMEOUT`, `LEAN_TRY_TIMEOUT`,
`LEAN_AUTO_TIMEOUT`, `LEAN_SEARCH_TIMEOUT`, `LEAN_OPEN_TIMEOUT`,
`LEAN_BUILD_TIMEOUT`, `LEAN_PROJECT_ROOT`, `LEAN_WORKDIR`, `LEAN_TASK_FILE`,
`LEAN_ENV_V2`, `LEAN_LOG_FILE`, `LEAN_LOG_META`, `LEAN_PORTFOLIO_EXTRA`,
`LEAN_MCP_DEBUG` (trace on stderr; stdout carries only JSON-RPC).

## 6. Phases and owners

| phase | deliverable | depends on |
|---|---|---|
| 1 scaffold + probe | lakefile, toolchain, `require repl`, `lake build` green; `Probe.lean` exe that, run under `lake env` in the Mathlib project, loads a file, creates a proof snapshot from a `sorry`, runs `nlinarith [sq_nonneg (x^3 - 1)]`, prints goals/status — proves the REPL API works on this toolchain | — |
| 2a Mcp + Proc | JSON-RPC loop, tool registry, JSONL log, process-with-timeout | 1 |
| 2b Text + Driver | parser-driven decl location/splitting, session engine (open/run/rollback/complete/build), availability, fuzzy names, timeouts | 1 |
| 2c Hints + Verify | hint table + synthesis (port from `prototype-python/src/lean_mcp_evolve/hints.py`), `lake build` + axiom audit + token scan | 1 (2a for Proc API) |
| 3 Session + Main | the nine tools, exact response texts (port `session_server.py`) | 2a, 2b, 2c |
| 4 tests | `Tests/Main.lean` = suites T/A/M mirroring the prototype's tests (same assertions), core project created on the fly; `lake exe tests` green, suite M green against LEAN_2026 | 3 |
| 5 docs + cleanup | README/DESIGN/ARCHITECTURE updated for the Lean-native design, CI (elan + lake build + lake exe tests), delete `prototype-python/` | 4 |

Review gates between phases are run by the planner: `lake build`, the
probe, then the test executable.

## Status

All five phases are complete.

- **Phase 1** (scaffold + probe): `lakefile.toml` requires
  `leanprover-community/repl @ v4.27.0-rc1`; `Probe.lean` confirmed the REPL
  API on this toolchain (prefix `processInput`, sorry → `ProofSnapshot`,
  `getProofStatus`, the wall-clock + `IO.CancelToken` timeout harness).
  Findings recorded in `docs/PHASE1_NOTES.md`, including the measured costs
  (cold `import Mathlib` open 44.1 s; warm rounds a few seconds for a
  Mathlib closer, sub-second for a core failure/timeout) and the
  `Core.checkInterrupted` cooperative-only limitation.
- **Phase 2a** (`Mcp.lean`, `Proc.lean`): newline-delimited JSON-RPC 2.0
  stdio loop, tool registry, JSONL instrumentation (`LEAN_LOG_FILE`/
  `LEAN_LOG_META`); process-with-timeout for `lake build`.
- **Phase 2b** (`Text.lean`, `Driver.lean`): parser-driven declaration
  location and tactic-unit splitting; the session engine on immutable
  `ProofSnapshot`s (open/evaluate/speculate/rollback/completion check/
  whole-file diagnosis); fuzzy did-you-mean over `env.constants`; the
  wall-clock + `CancelToken` + `maxHeartbeats` timeout harness.
- **Phase 2c** (`Hints.lean`, `Verify.lean`): the error-hint table and
  `nlinarith`/`positivity` hint synthesis (ported from the Python
  prototype's `hints.py`); `lake build` + `collectAxioms` axiom audit +
  forbidden-token scan for `verify`.
- **Phase 3** (`Session.lean`, `Main.lean`): the nine tools wired up with
  response texts, tool descriptions and input schemas ported from
  `session_server.py`.
- **Phase 4** (`Tests/`): `lake exe tests` — suite T (12 cases, 35 checks,
  pure), suite A (19 cases, 95 checks, spawns the real server against a
  core-only project), suite M (5 cases, 29 checks, Mathlib-backed, skipped
  without `LEAN_MCP_TEST_MATHLIB_PROJECT`).
- **Phase 5** (this phase): README/DESIGN/ARCHITECTURE rewritten for the
  Lean-native design; `.github/workflows/ci.yml` builds and runs suites T
  and A (M needs a pre-built Mathlib project, run manually); `prototype-python/`
  left in place for the planner to remove.

### Hardening (2026-09-05)

- **Out-of-process correctness gate** (`LeanMcpEvolve.Gate`/`GateMain`, the
  Lean analogue of rocq-mcp-evolve's `harness/gate.py`): a fresh `lean_exe`
  (`lake exe gate <candidate.lean> --theorem <name> [--reference <file>]
  [--project <root>] [--json]`) that re-derives acceptance from nothing but
  the candidate's source text, in its own process, in six steps —
  reference/statement tamper, forbidden tokens on the parsed `Syntax` tree,
  a fresh compile (`cmdState? := none`), target/type validity, a
  `collectAxioms` allowlist audit, and kernel replay via Lean core's
  `Lean.Environment.replay` (adapted, with attribution, to report which
  constant the kernel rejected). Exists because a tactic block runs in the
  *same process* as the in-session checks and can run arbitrary
  metaprograms (`run_tac`, `Lean.addDecl`,
  `Lean.Kernel.Environment.addDeclWithoutChecking`) — see `docs/DESIGN.md`
  §3b for the full Rocq → Lean step mapping.
- Wired into the server as an opt-in hook: `LEAN_GATE=1` (+ optional
  `LEAN_GATE_BIN` override) runs the gate against every completion's
  `candidate.lean` before the agent is told `PROOF COMPLETE`
  (`Session.runGateCheck`/`completeMsg`). Fail-closed once enabled: only a
  clean exit 0 with `ACCEPTED` counts as a pass; anything else (missing
  binary, non-zero exit without a `REJECTED:` line, timeout, malformed
  output) is `gate_unavailable:<detail>`, treated exactly like a real
  rejection — the last committed unit is rolled back and `candidate.lean` is
  deleted.
- Documented residual risks (README "Verification" section): the gate
  trusts the Lean binary and the project's already-built `.olean`s
  (a tampered dependency `.olean` is out of scope, as for the Rocq gate);
  `example` targets can't be gated (`target_is_example`); the reference
  comparison is textual outside the proof region plus an `Expr`-level type
  comparison of the target only, never the proof term itself; and the
  `blankMathlibImportLine` parse-only workaround can, on a project without
  Mathlib, fail to locate a proof that relies on genuinely new syntax
  `Mathlib.Tactic` introduces, in which case the token check passes
  conservatively and steps 3–6 are the actual backstop (regression: D9).
- New suite **D** (`Tests/Gate.lean`, 9 cases D1–D9, 33 checks), run by
  default under `lake exe tests` alongside T and A: legit accept,
  placeholders (`sorry`/`sorryAx`), statement/prefix tamper, the Rocq D4
  comment/string desync exploit, `native_decide`'s hidden axiom, an
  injected axiom via `run_tac`, an unchecked `addDecl` smuggle caught only
  by kernel replay, missing target, and the one tolerated
  `import Mathlib.Tactic` header line. Several cases drive the library API
  directly with the forbidden-token check disabled to prove steps 3–6
  independently reject what step 2 would already have caught.
- Suite **A** grew four cases, A21–A24 (23 cases / 113 checks total, up from
  19/95): in-session axiom injection via `run_tac` (caught by
  `completionCheck`'s fail-closed axiom audit, with and without
  `LEAN_ENV_V2`), `native_decide` refused unconditionally, `example`
  completion audited under a synthetic name instead of best-effort-passing
  on a failed lookup, and `sorryAx` spelled directly still never completing.
- `Driver.completionCheck` and `Session.rejectForbidden`/`alwaysForbidden`/
  `envV2Forbidden` reviewed and confirmed fail-closed end to end: the
  completion audit re-elaborates with `debug.skipKernelTC` forced off
  regardless of session state, fails closed (not best-effort `true`) when
  the target constant can't be found post-re-elaboration (including the
  `example` case via `spliceExampleKeyword`), and `sorryAx`/`native_decide`/
  `ofReduceBool`/`ofReduceNat`/`addDeclWithoutChecking` are refused
  up front regardless of `LEAN_ENV_V2`.

### Refusal parity (2026-09-06)

Full parity with rocq-mcp-evolve's session server, on both axes it refuses/
accepts things: what is refused UP FRONT, and what counts as COMPLETE
in-session. Both were previously stricter than the Rocq server; both are now
exact matches, by design — a benchmark harness comparing the two servers
must see the same refusal/acceptance surface, with only the out-of-process
gate (run by the harness itself, same as Rocq's `harness/gate.py`) deciding
actual correctness.

- **Up-front refusals** (`Session.rejectForbidden`): refuses exactly ONE
  thing — `import` (the Lean analogue of `Require`, since Lean has no
  mid-file import statement either), detected on comment/string-stripped
  text as a line whose first token is the keyword `import`, only when
  `LEAN_ENV_V2=1` — bit-for-bit parity with `reject_require`'s `Require`
  under `ROCQ_ENV_V2=1`. The old always-on `alwaysForbidden` list (`sorryAx`,
  `native_decide`, `ofReduceBool`, `ofReduceNat`, `addDeclWithoutChecking`)
  and the wider `envV2Forbidden`/`envV2IdentForbidden`/`substrOnlyForbidden`
  metaprogramming/escape-hatch surface are deleted outright. The `hint:`
  table is untouched (advice, not a refusal).
- **In-session completion** (`Driver.completionCheck`): reduced to exactly
  what the Rocq server's own session server checks — goals empty AND the
  finished declaration re-elaborates with NO error messages (kernel checking
  forced on, as before). The old four-layer check (REPL's `getProofStatus`
  gate, a `sorry`-warning veto, a `collectAxioms` allowlist, and a
  constant-lookup audit) is gone from this function; `getProofStatus` stays
  defined in `Driver.lean` (the gate and tests use it) but is no longer
  called from `completionCheck`. Consequence: `sorry`, `native_decide`, an
  axiom injected via `run_tac`, `exact (sorryAx _ false)`, etc. all EXECUTE
  and, once they close the goal, are reported PROOF COMPLETE with
  `candidate.lean` written — exactly as the Rocq server accepts `Admitted.`
  in-session. `try` commits such a candidate as a full success; `auto_close`
  counts it as a win. Catching this class of "proof" is now entirely the
  standalone gate's job (`lake exe gate`, unchanged, run by the harness after
  the fact) — never this refusal layer's, and never the in-session check's.
  `LEAN_GATE=1` remains as the one Lean-only addition: an opt-in hook that
  runs the same gate *in-session* for interactive convenience, off by
  default, with no Rocq equivalent (the Rocq protocol only ever runs its
  gate from the surrounding harness).
- **Default configuration is the Rocq server's own default**: with no
  `LEAN_*` variables set at all, all nine tools and every enrichment are on,
  nothing is refused up front (`LEAN_ENV_V2` off, like `ROCQ_ENV_V2`), and
  `LEAN_GATE` is off — in-session PROOF COMPLETE means "closed and
  elaborates," and correctness is decided by whatever runs `lake exe gate`
  afterwards. New case A28 spawns with only `LEAN_WORKDIR` set (no
  `LEAN_TASK_FILE`, no `LEAN_ENV_V2`) and checks exactly this.
- Suite A: A7 rewritten ("ENV_V2 refuses import, nothing else; `sorry`
  executes to PROOF COMPLETE"); A21/A22/A24 rewritten as genuine parity
  tests — in-session PROOF COMPLETE + `candidate.lean` written, THEN the
  built `gate` executable is run against that candidate from the test
  (mirroring the harness step a real benchmark would run) and asserted
  `REJECTED:` (forbidden token / injected axiom, per `Tests.Gate`'s D2/D5/D6
  for the same classes); A25 rewritten (`try ["sorry", "omega"]` commits
  `sorry` itself as the first full success, not `omega`); A26 (the old
  `auto_close`-pseudo-closure regression, no longer applicable) dropped; new
  A27 exercises the opt-in `LEAN_GATE=1` hook end to end (a `sorry` that
  would complete in-session is instead rejected by the gate before the agent
  ever sees PROOF COMPLETE, with a rollback); new A28 covers the
  no-environment-variables default. 28 cases / 141 checks total, up from
  23/113. Suites T (35/35) and D (49/49) are unaffected: `Text.lean`,
  `Verify.lean` and `Gate.lean` were not touched by this change.

### `lake env` bootstrap (2026-09-06)

- `LeanMcpEvolve/Reexec.lean`: both executables (`lean-mcp-evolve`, `gate`)
  re-exec themselves as `lake env <self> <argv>` from the project root when
  `LEAN_PATH` is unset (server: `LEAN_PROJECT_ROOT`, else the `LEAN_TASK_FILE`
  preset's lakefile ancestor; gate: `--project`, else the candidate's). Found by
  the PutnamBench harness (`testing/`), which launches the binaries directly:
  the REPL's `processInput` and `Text.findDecls`'s header processing re-derive
  the search path from the environment, and `lean --print-prefix` outside a
  project resolves elan's default toolchain, so `import Mathlib` files were
  elaborated against a core-only / mismatched environment ("pattern-matching
  decl" refusals, spurious gate `compile_error`s). `LEAN_NO_REEXEC=1` opts out.
- `Text.findDecls` scope tracking (2026-09-06): the parse-only declaration
  locator now replays standalone `open` (all five `openDecl` forms) /
  `namespace` / `section` / `end` commands on the parser state as it walks the
  file — `Lean.activateScoped`/`pushScope`/`popScope` on the environment plus
  `currNamespace`/`openDecls` in the `ParserModuleContext` — so scoped
  notations activated earlier in a file (`open Nat` then `n !`, `open scoped
  Real` then `π`) parse. Before, such declarations parsed without a body and
  `open` refused them as "pattern-matching decl" (5 of the 60 PutnamBench
  files). Tests T13/T14 (`Tests/Text.lean`, core-only, via `List`'s scoped
  `<+`). `open X in <decl>` was already handled by Lean's parser.
- Eager open of the preset task file (2026-09-07): with `LEAN_TASK_FILE`
  set, `Main` starts the open in the background (`Session.startEagerOpen`,
  `IO.asTask (prio := .dedicated)`) before serving MCP, so the `import
  Mathlib` + statement elaboration (~40-70 s) overlaps the handshake and the
  model's first turn instead of landing inside the first tool call — parity
  with the Rocq server, which has the statement executed at launch.
  `getSession`/`open` wait on the in-flight task, never open twice;
  `LEAN_EAGER_OPEN=0` disables. Tests A30/A31. Lesson: the open must run on a
  DEDICATED thread — on a pool worker it starved the nested elaboration task
  `Driver.waitTask` polls for, and the process then hung at exit in
  `lean_finalize_task_manager` (every suite-A server leaked).
- `Driver.suggestNames` bounded (2026-09-07): no suggestions for short names
  under 3 characters; cheap length/fragment prefilter before any fuzzy call;
  scan budget (150 000 constants examined or 300 hits). A 1-character unknown
  identifier had cost 160 s of wall inside a `try` call on Mathlib.
- Benchmark harness: `testing/` (README there) — the rocq-mcp-evolve miniF2F
  held-out protocol ported to `dataset/` (PutnamBench-60); two extra
  `lean_exe`s under `testing/servers/` (`lean-mcp-baseline`, `lean-mcp-submit`)
  are the naive-control and submit-sidecar servers.

### Placeholder refusal restored (2026-09-08)

Corrects a false parity claim from the 2026-09-06 "refusal parity" change
(above): that change had `sorry`/`sorryAx`/`admit` EXECUTE and, once they
closed the goal, report PROOF COMPLETE, reasoning that rocq-mcp-evolve's own
session server accepts `Admitted.` in-session exactly as it accepts a real
`Qed.`. Found false: the Rocq server's completion signal is "a `Qed.` was
submitted and it succeeded" — `Qed.` FAILS after `admit`, and `Admitted.`
(a distinct vernacular command the tactic-running tools never submit) is
what actually completes a Rocq "proof" the old design let `sorry` do. There
was never an in-session "placeholder completes" behaviour on the Rocq side
to have parity with.

- **Up-front placeholder refusal** (`Session.firstSorryUnit`/
  `Text.sorryHit`, unconditional, never gated by `LEAN_ENV_V2`): a tactic
  unit whose PARSED syntax contains the atom `sorry` or the identifier
  `sorryAx`/`admit` is refused before it ever executes, in `step`/`try`/
  `check`. Decided on the unit's own parsed `Syntax` (adapted from
  `Gate.lean`'s `forbiddenHits` walker, added independently to `Text.lean`
  since `Gate.lean` depends on `Text.lean`, not the reverse), so a `sorry`
  in a comment or a string literal is untouched, while a nested
  `have h : P := by sorry` inside a longer unit is still caught. `step`/
  `check` follow commit-good-prefix (earlier units stay committed, the
  offending unit reports as an ERROR reusing the existing error-rendering
  shape, nothing after it runs); `try` rejects the whole candidate as an
  error, never committed. Log field `stop: "sorry_rejected"` on the
  `tool_call` record. `auto_close`'s finisher portfolio and hint-synthesis
  (`Driver.goalFacts`/`Hints.synthCandidates`) were checked and left
  unguarded: both build candidates purely from hypothesis/variable NAMES and
  `MetaM`-pretty-printed structural facts, never from arbitrary user text,
  and `sorry` cannot be used as an identifier (it's a reserved keyword), so
  there is no realistic injection path into that portfolio.
- **`Driver.completionCheck` restored to a real audit** (README
  "Verification" §1): goals empty; re-elaboration (kernel-checked) produces
  no error AND no `declaration uses 'sorry'` warning (`isSorryWarningMsg`);
  `Lean.collectAxioms` of the re-elaborated target ⊆ `{propext,
  Classical.choice, Quot.sound}`. `example` targets are spliced into
  `theorem <synthetic name>` first (`spliceExampleKeyword`) since `example`
  elaborates under a transient name (`_example`) never added to the
  environment permanently; the audit fails CLOSED if that constant still
  can't be found. Consequence: A21's `run_tac`-injected `cheat` axiom and
  A22's `native_decide` (`Lean.ofReduceBool`) no longer reach PROOF COMPLETE
  in-session at all — previously they did, with the standalone gate as the
  only backstop.
- **The standalone gate keeps genuine, demonstrated value**: A27 was
  rewritten around an "unchecked smuggle" (`run_tac` locally overrides
  `debug.skipKernelTC` back to `true` around one `Lean.addDecl` call, adding
  an ill-typed constant the kernel never checks) that fools
  `completionCheck`'s re-elaboration exactly as it fooled the live session
  (same process, same script) — only `lake exe gate`'s independent,
  separate-process, kernel-replaying checks catch it (here: at its own
  earlier forbidden-token step, since `run_tac` is itself forbidden; see
  `Tests.Gate`'s D7 for the deeper kernel-replay layer underneath, with the
  token check bypassed).
- Suite A: A7 rewritten (bare `sorry` refused, comment/string-literal
  `sorry` NOT refused, `stop:sorry_rejected` logged); new A7b (nested
  `have h : P := by sorry` refused with commit-good-prefix); A21/A22
  rewritten (refused in-session now, via the axiom audit, not just by the
  gate afterward); A24 rewritten (`sorryAx` refused up front, same as bare
  `sorry`); A25 rewritten (`try ["sorry", "omega"]` reports `sorry` as an
  error, commits `omega`); A27 rewritten around the unchecked-smuggle
  scenario above; A28 rewritten (`sorry` refused by default too, since the
  refusal is unconditional). 32 cases / 221 checks total for suite A.
  Suites T (42/42) and D (49/49) are unaffected: `Text.lean`
  gained the new `sorryHit` walker as an ADDITION (`splitUnits` itself is
  untouched), and `Gate.lean` was not touched at all. `lake build` then
  `lake exe tests` (suites T/A/D, core-only): 312 passed, 0 failed.

### Known discrepancies from the Python prototype (reported by Phase 3)

The ported behaviour follows this PLAN document rather than the Python
prototype's exact wording/scan set wherever the two disagree:

- `open`'s error wording for rare filesystem-error paths follows this PLAN,
  not the Python prototype's exact phrasing.
- Lean's own diagnostic messages carry a `file:line:col:` prefix that the
  Python prototype's Rocq-derived message texts did not.
- `verify`'s forbidden-token scan checks 4 tokens (`sorry`, `admit`,
  `axiom`, `native_decide`); the axiom audit (`collectAxioms`) independently
  catches `sorryAx`/`Lean.ofReduceBool`, which is a superset of what the
  Python prototype's 8-token `FORBIDDEN_TOKENS` tuple covered by scanning
  text alone.
- The "N previously committed tactic(s) discarded" fresh-attempt note on
  `check` also fires when N = 1 (a single discarded tactic), not just N ≥ 2.
- `verify`'s project-root resolution (`LEAN_PROJECT_ROOT` > opened session's
  root > cwd) tracks only the currently opened session, not a
  previously-opened-then-closed one.
- `step`/`try`'s splicing of a search tactic's `Try this:` suggestion is
  first-occurrence textual (the first match of the suggested tactic's own
  text), not a true source-position substitution.
