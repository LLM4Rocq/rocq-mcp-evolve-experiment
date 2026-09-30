# Design: porting rocq-mcp-evolve's tool layer to Lean 4

This document maps every design decision of rocq-mcp-evolve (the Rocq server
this project adapts) to its Lean 4 realisation, and records what had to
change because the two provers expose different primitives. The tool
*surface* is frozen — exactly the nine default-on tools of the Rocq server —
so every adaptation lives inside a tool's behaviour, never in a new tool.

## 1. Why in-process Lean rather than the language server

An earlier prototype of this server drove `lake serve` (the language
server) over LSP: it needed no toolchain match beyond what `lake build`
already requires, and its incremental elaboration reuses an unchanged
prefix cheaply. But its state is "the text of a document so far," not a
first-class value — rollback means re-rendering a shorter document and
waiting for diagnostics again, and every round pays a full diagnostics
round trip through the server's own scheduler.

The product now links the [community REPL](https://github.com/leanprover-community/repl)
library and drives Lean **in-process**, exactly as the Rocq server links
Rocq in-process:

- **Same-toolchain constraint, accepted.** The server can only load
  `.olean`s built by the same Lean version as the target project — inherent
  to any in-process Lean tool (the REPL itself, Pantograph, LeanDojo all
  share it), and it is the same contract the Rocq server already has
  ("build your project first"). Users build this server with the toolchain
  of the project they want to work on.
- **Immutable snapshots give O(1) rollback and trivially independent
  speculation.** `REPL.ProofSnapshot` is an immutable value — the Lean
  analogue of Rocq's `Vernacstate.t`. `Session.committed` is a list of
  `(tactic, ProofSnapshot)` pairs, newest first; `rollback n` is `List.drop
  n`, and `try`'s k candidates each run from a fresh reference to the same
  snapshot, so evaluating one never disturbs another (`Driver.speculate`).
  No document re-render, no waiting for a scheduler to settle.
- **Kernel-checked completion, not a sentinel.** A finished proof is
  checked by (1) the tactic state having no open goals, (2) `REPL`'s
  `getProofStatus = "Completed"` (the kernel type-checks the produced proof
  term), (3) re-elaborating the finished declaration text as a command in
  the prefix state produces zero errors and no `declaration uses 'sorry'`
  warning, and (4) `Lean.collectAxioms` of the declared constant contains
  neither `sorryAx` nor `Lean.ofReduceBool` (`Driver.completionCheck`). All
  four must hold — this is strictly more checking than a document-based
  sentinel can give you for free, because the constant and its axiom set
  are addressable values here, not text.
- **No per-round document re-elaboration.** Each `step`/`try`/`check`/
  `auto_close` round runs exactly the tactic text submitted, against the
  exact snapshot it was submitted from — never a whole-file or whole-prefix
  re-elaboration (that cost is paid once, at `open`, via
  `Lean.Elab.IO.processInput` on the prefix, and cached per `(file,
  prefixText)` in `Driver.prefixCache`).

The cost of all this is the same-toolchain constraint above, and that
`REPL.Main` cannot be imported directly (its own `main` would collide with
ours — see `docs/PHASE1_NOTES.md`), so two of its functions
(`getProofStatus`, the sorry→`ProofSnapshot` half of `REPL.sorries`) are
copied into `Driver.lean` with attribution rather than imported.

## 2. Tool by tool

| Rocq | Lean 4 | what changed |
|---|---|---|
| `open{file, theorem?}` executes the file up to the statement, `Admitted`-ing earlier broken proofs | `Driver.openFile` parses the file with Lean's own parser (`Text.findDecls`) to locate the target, elaborates the prefix once (`Lean.Elab.IO.processInput`, `cmdState? := none`), then elaborates `stmtText ++ " sorry"` in that prefix state and pulls a `ProofSnapshot` out of the resulting info tree's `sorries` (`REPL.ProofSnapshot.create`) as `base` | Lean admits broken earlier declarations *natively* via its own error recovery (they get `sorryAx`-backed proofs), so "reach any theorem" costs nothing extra. Default target = first declaration whose whole-file elaboration reports an error or `sorry`, since Lean proofs have no trailing open goal to look for the way Rocq's do. |
| `build{file}` admit-and-continue walk | one whole-file `processInput` under a throwaway `Command.State`; diagnostics grouped by declaration range (`Driver.diagnoseCore`/`diagnoseFile`): errors and `sorry` warnings both become a hole | pure by construction (a separate elaboration, the live session's `Command.State` untouched); every hole in one call is Lean's normal error-recovery behaviour, not something the driver has to orchestrate. |
| `check{script}` fresh attempt from the base state | committed list rolled back to empty (`Driver.rollback s0 s0.committed.length`), script split into units by the tactic-sequence parser, one `Driver.evaluate` from `base` | leading `by` tolerated by the parser; failure phrasing says "repair from here (step/try/auto_close) or rollback and resubmit" (`Session.checkToolHandler`). |
| `step{text}` commit-good-prefix; `#`-queries run but are not committed | units = top-level tactics from `Lean.Parser.Tactic.tacticSeq`/category `tactic` (bullets, `induction … with` alternatives, bracket/`<;>` continuations each one unit — parser-driven, not indentation-driven); `#check`/`#print`/`#eval` lines are run via `Driver.runQuery` against the current snapshot's state and reported, never committed | search tactics (`exact?`/`apply?`/`rw?`/`simp?`) are re-run as the tactic string found in their `Try this:` message and *that* is what gets committed (`Text.parseTryThis` + a second `runUnitWithTimeout`) — no diagnostic-position splicing needed, since we already hold the snapshot the suggestion came from. |
| `try{candidates}` k speculative scripts, first full success commits | every candidate evaluated independently via `Driver.speculate` from the *same* `base`/current snapshot (an immutable value, so this is just "run from a copy"), then the first fully-successful one is re-applied with `Driver.evaluate` to actually commit it | identical semantics to Rocq; the speculative pass costs nothing extra to make independent, since nothing is mutated by evaluating a snapshot. |
| `auto_close{}` portfolio + synthesized `0 <= (t)^2` facts, progress rule | portfolio `rfl/trivial/simp/omega/decide/norm_num/linarith/nlinarith/positivity/ring/field_simp+ring/simp_all/aesop/tauto/bound/gcongr/norm_num [*]/intros+linarith/intros+nlinarith`, filtered by parse-availability (`Driver.availableTactics`, an `example : True := by <tac>` probe against the session's own environment), then synthesized `nlinarith [...]`/`positivity` candidates, then `exact?` last | **hint synthesis reads the `MetaM` local context and goal directly** (`Driver.goalFacts`: arithmetic-typed hypotheses, `0 < _`/`0 ≤ _` shapes via `getAppFnArgs`, even powers in the conclusion via a recursive `Expr` walk) rather than regex-scanning a printed goal string — the Python prototype had no other option, this port does because it already has the `MetaM` context in hand. `exact?` is committed as its own `Try this:` suggestion, same mechanism as `step`. |
| `rollback{count}` O(1) state swap | `List.drop count` on `committed` | truly O(1): no re-render, no re-elaboration. |
| `state{}` full re-render | cached goals from the current snapshot (`ProofSnapshot.ppGoals`) + the committed script | no round trip into the prover at all. |
| `verify{}` `dune build` + forbidden-token scan via Rocq's lexer | `lake build` (`Proc`-run, lock-file-serialised) + `Verify.axiomAudit` (import every module of the target project, `Lean.collectAxioms` every constant it declares, flag `sorryAx`/`Lean.ofReduceBool`/non-standard axioms under `LEAN_ENV_V2`) + a comment/string-aware scan for `sorry`/`admit`/`axiom`/`native_decide` | the axiom audit is new relative to the Python prototype, which never ran inside a Lean process and so had no way to call `collectAxioms` at all — this is the one place the Lean port does strictly more than what it otherwise mirrors verbatim (see `Verify.lean`'s module doc). |

## 3. Enrichments (zero marginal turn cost)

- **Error hints** (`LEAN_HINTS`): the table rewrites Rocq/Coq-isms (`intros
  x.`, `lia`, `nra`, `destruct`, `assert`, `rewrite`, `Search`, `Qed`) and
  Lean 3-isms (`cases h with a b`, `rw h`, `λ x, e`, `{ }` focusing) into
  Lean 4, plus message-keyed advice (`linarith failed` → try
  `nlinarith`/`positivity`; `omega could not prove` → scope; `simp made no
  progress`; `motive is not type correct`; heartbeat timeouts; trailing
  period). Ported verbatim from the earlier Python prototype's hint table (since removed)
  into `Hints.lean` as pure `String → String` functions; the caller
  (`Session.lean`) checks `Hints.hintsOn`/`suggestOn`/`auto2On` itself before
  calling them, since a pure function has no way to consult an env var
  (see `Hints.lean`'s module doc).
- **Did-you-mean** (`LEAN_SUGGEST`): the language server's `workspace/symbol`
  fuzzy search has no equivalent to call out to in an in-process design, so
  `Driver.suggestNames` calls the same underlying scorer directly —
  `Lean.FuzzyMatching.fuzzyMatchScoreWithThreshold?` — over every constant
  name in `env.constants`, also tried against shrinking prefixes of the
  unknown identifier (typo-tolerant), plus a shared-fragment
  (snake_case/CamelCase split) and same-namespace bonus, exactly the ranking
  the prototype's difflib-based version used.
- **Hint synthesis** (`LEAN_AUTO2`): see `auto_close` above — `Driver.goalFacts`
  supplies the raw `(hypothesis name, arithmetic type)` / `(hyp, "0 < e")`
  / `(base, exponent)` facts from the real `MetaM` context, and
  `Hints.synthCandidates` formats them into `nlinarith [sq_nonneg (x ^ 3 -
  1), …]`/`positivity` scripts (half-exponent pairing, de-duplication, a cap
  of 4 facts) — the same shaping the Python prototype did on regex-matched
  substrings of a printed goal.
- **Tactic preloading** (`LEAN_PRELOAD`): when the project depends on
  Mathlib (a `.lake/packages/mathlib` under the root) and the file imports
  neither `Mathlib` nor `Mathlib.Tactic`, `Driver.openFile` injects `import
  Mathlib.Tactic` after the existing import block for the session (retried
  without it if that import itself fails to resolve). The **import echo**
  (`LEAN_IMPORT_ECHO`) then tells the agent, on completion, which Mathlib
  tactics the finished proof actually used and to add the import line
  itself; `candidate.lean` already carries it.
- **Forbidden placeholders up front**: `sorry`/`admit` in agent-submitted
  text are refused before any elaboration is attempted
  (`Session.rejectForbidden`) — a tactic that "closes" a goal by giving up
  can never help. `LEAN_ENV_V2=1` additionally refuses `native_decide`,
  `set_option`, `import`, `axiom`, `Lean.ofReduceBool`, `decide +native`.
  This is enforced again, independently, at completion: `collectAxioms` on
  the finished declaration must not contain `sorryAx`/`Lean.ofReduceBool`
  (§1 above), so a placeholder that slipped past the text check some other
  way still fails to complete.
- **Hang safety**: every tactic runs on `IO.asTask`; the caller polls
  `IO.hasFinished` against a wall-clock deadline
  (`LEAN_STEP_TIMEOUT`/`LEAN_TRY_TIMEOUT`/`LEAN_AUTO_TIMEOUT`/
  `LEAN_SEARCH_TIMEOUT`) instead of blocking on `task.get`; on a miss an
  `IO.CancelToken` installed in `Core.Context.cancelTk?` is set (tactics
  check it cooperatively in `Core.checkSystem`) and the call simply stops
  waiting and reports TIMEOUT. **Measured limit** (`docs/PHASE1_NOTES.md`):
  `Core.checkInterrupted` is checked only *between* elaboration steps, so it
  cannot interrupt one opaque kernel reduction that never yields — a
  runaway `decide` keeps its worker thread running past the deadline; the
  wall-clock mechanism keeps the *server* responsive by abandoning the wait,
  not by actually stopping the stray computation, and process exit is what
  eventually reclaims a leaked thread. `Core.Context.maxHeartbeats` is left
  at Lean's own default (200000, not raised — `LEAN_MAX_HEARTBEATS`) so it
  remains a second, deterministic guard independent of wall-clock timing.

## 3b. Correctness gate (rocq-mcp-evolve suite D analogue)

`LeanMcpEvolve.Gate`/`GateMain` (wired into the server as the optional
`LEAN_GATE=1` hook, `Session.runGateCheck`/`completeMsg`) is the Lean
analogue of rocq-mcp-evolve's `harness/gate.py` and its suite D tests: an
out-of-process, anti-gaming recompile of a candidate that trusts nothing the
in-session process itself computed. It exists for the same reason the Rocq
one does — a tactic block executes arbitrary code in the *same process* as
the checker (`run_tac`, `Lean.addDecl`,
`Lean.Kernel.Environment.addDeclWithoutChecking` on the Lean side; an
equivalent metaprogramming surface on the Rocq side), so a second opinion
from a fresh process that only reads the candidate's source text is the only
check that can't be corrupted by the very thing it's checking.

| Rocq gate check | Lean gate step (`Gate.runInternal`) |
|---|---|
| fresh recompile of the candidate file (a clean `coqc`/`dune build`, not reusing any state the candidate's own run might have left behind) | step 3: `Lean.Elab.IO.processInput candSrc none {} ..` (`cmdState? := none` — a genuinely fresh `Command.State`, not the session's) |
| forbidden tokens decided on Rocq's own lexer output, not a hand-rolled text scan (so a token can't be hidden/faked by a comment or string trick) | step 2: forbidden tokens decided on Lean's own parsed `Syntax` tree (`forbiddenHits` over `Lean.Parser`'s output) — same principle, Lean's tokenizer/parser standing in for Rocq's lexer |
| prefix/statement tamper check — the candidate may only change the target's proof, nothing else in the file | step 1: `checkTamper` — every declaration outside the target must match the reference textually (one tolerated `import Mathlib.Tactic` header line aside), and the target's own statement text must be byte-identical |
| `Print Assumptions` on the closed theorem — Rocq's command for listing every axiom in a term's transitive dependency closure | step 5: `Lean.collectAxioms` of the target, required to be a subset of `{propext, Classical.choice, Quot.sound}` — the same idea, called through Lean's library function instead of a REPL command |
| the D4 desync exploit — a `sorry`/forbidden token straddling a comment or string boundary, defeating a naive text scanner | can't happen on the Lean side by construction: step 2 walks parsed `Syntax` (comments never make it into the tree), and step 3's fresh compile independently re-parses from scratch — either the token is really there and step 2 catches it, or the "trick" broke the parse and step 3's `compile_error` does. Regression: D4 in `Tests/Gate.lean`. |

**Step 6, kernel replay, is the one check with no Rocq analogue in the
harness** — short of running `coqchk` (Rocq's standalone, offline checker
that re-validates compiled `.vo` object files against the trusted kernel,
independent of `coqc`'s own elaboration/type-checking pass, but not normally
invoked as part of an interactive proof loop). Lean ships the equivalent
machinery as a library call: `Lean.Environment.replay` re-adds every
constant a candidate declared through the kernel (`Environment.addDeclCore`,
`doCheck := true`, never `addDeclWithoutChecking`) into a fresh environment
built only from the candidate's own header imports, correctly threading
inductive/constructor/recursor dependencies via the `ConstantInfo`s already
in hand. `Gate.lean`'s `Replay` namespace is that exact algorithm, copied
from `Lean/Replay.lean` (© 2023 Kim Morrison, Apache 2.0) with one change:
tagging a kernel rejection with the name of the constant that caused it
(`replay` itself discards that once it throws), so the gate can report
`kernel_replay_failed:<name>:<msg>` rather than just "replay failed
somewhere." This is exactly the "inductive replay … when feasible" capability
the original task briefing flagged as an open problem for a from-scratch
implementation — except Lean core already ships it, so the Lean gate gets a
capability the Rocq one has no cheap way to reach for free.

Test regression D7 (`Tests/Gate.lean`) is the case this step exists for: a
`run_tac` block sets `debug.skipKernelTC` and then `Lean.addDecl`s an
ill-typed "theorem" built from hand-constructed `Expr`s — something only the
kernel (never the elaborator's ordinary type inference, since there is no
elaboration happening) would reject. With the forbidden-token check bypassed
(`runInternal`'s test-only flag), steps 3–5 all pass (the file compiles, the
target exists with the right type, and no non-standard axiom was added — the
smuggled constant isn't even an axiom); only step 6's kernel replay catches
it, with reason `kernel_replay_failed:cheat`.

## 4. Things deliberately not ported

- `search` tool — off by default in the Rocq server (a pull tool that lost
  the turn-cost ablation); `exact?`/`apply?` as steps and the did-you-mean
  push cover the need without a tool.
- Compact goal rendering (`ROCQ_RENDER=compact`) — measured worse (+27% cost
  per solve) in the Rocq experiment; full rendering is the only mode here.
- Exemplar retrieval (`ROCQ_EXEMPLARS`) — measured neutral; not built.
- The multi-agent daemon — removed upstream after a negative result.
- mathcomp bridges — no Lean analogue; Mathlib tactics are the ambient
  environment already.

## 5. Costs to know about

Measured on `v4.27.0-rc1` against `/Users/jviennot/Documents/Cours/LEAN_2026`
(a Mathlib-backed project) — see `docs/PHASE1_NOTES.md` for the raw numbers.

| operation | measured cost |
|---|---|
| `open` on a new file, cold page cache, `import Mathlib` + a tactic that closes the goal | **44–65 s** wall (dominated by loading Mathlib's `.olean`s the first time) |
| a Mathlib-closing tactic round (`nlinarith`, warm cache) | a few seconds |
| a parse-error / tactic-failure round on a core (no-Mathlib) goal, warm cache | sub-second |
| a `decide` under a short budget that has to be abandoned | the full budget, plus ~a few seconds of process overhead (measured: 3 s budget → TIMEOUT reported at 9.3 s total) |
| `build` / `verify` | one whole-file elaboration (`build`), or a full `lake build` of the project (`verify`, `LEAN_BUILD_TIMEOUT` 600 s default) |

The prefix state for a given `(file, prefixText)` pair is cached in-process
(`Driver.prefixCache`), so re-opening the same file (e.g. to target a
different theorem) after the first `open` does not pay the prefix
elaboration cost again within the same server process.
