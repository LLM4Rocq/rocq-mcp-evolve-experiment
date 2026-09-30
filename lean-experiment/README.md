# lean-mcp-evolve — rocq-mcp-evolve's tool layer, for Lean 4

A **policy-neutral MCP tool layer** that lets an LLM agent drive the Lean 4
prover, adapted one decision at a time from
[rocq-mcp-evolve](https://github.com/LLM4Rocq/rocq-mcp-evolve) — the
empirically-designed Rocq server whose every tool and enrichment was kept or
reverted on measured pass@1 / cost / wall-clock deltas. The tool set here is
**exactly** the Rocq server's shipped set (nine tools, no more, no less), so
the two servers can be compared under one harness; what differs is the engine
underneath and the Lean-specific content of the enrichments.

Unlike the earlier prototype (and unlike `lake serve`/LSP-based tools), this
server drives Lean **in-process**, the way the Rocq server drives Rocq
in-process: it links the [community REPL](https://github.com/leanprover-community/repl)
library and keeps an immutable `REPL.ProofSnapshot` per committed tactic — the
Lean analogue of Rocq's `Vernacstate.t` snapshots. Written entirely in Lean 4
(a Lake package, one executable). Per-decision rationale:
[`docs/DESIGN.md`](docs/DESIGN.md).

> The design law inherited from the Rocq ablations: *maximize prover-grounded
> information per model turn, at zero marginal turn cost.* Everything that
> pushes information into existing turns (speculative `try`, finisher
> portfolio + hint synthesis, error hints, did-you-mean, preloading) is in;
> nothing that spends a turn to fetch it (a pull search tool) is.

## The tools — one server (`lean-mcp-evolve`)

The agent talks MCP over stdio. Whole-proof and incremental styles are both
first-class. All tools and enrichments are ON by default (trim with
`LEAN_ENABLE_TOOLS`, disable features with `LEAN_<FEATURE>=0`).

| tool | what it does |
|---|---|
| `build{file}` | Diagnose a whole file in one call: every declaration is elaborated, a broken proof is admitted so dependents still check — you get **all** broken proofs (errors and `sorry`s) at once, then fix each via `open`. Purely diagnostic; never touches the live session. |
| `open{file, theorem?}` | Open a `.lean` file and start (or restart) a session on it: targets the named theorem's statement (its old proof / `sorry` is ignored, earlier broken proofs are admitted so every theorem is reachable) or, by default, the first declaration that errors or uses `sorry`. The project (lakefile) is discovered from the file's location. |
| `check{script}` | Submit a **complete** tactic script in one call, from the base state. On success, done; on failure the valid prefix stays committed and you stand at the failing tactic with the live goal — repair or resubmit. |
| `step{text}` | Execute one or more tactics incrementally (one per line; bullets and `induction … with` blocks are single tactics — split by Lean's own tactic-sequence parser, not indentation heuristics); each success commits permanently, the first failure reports a structured error and leaves the state at the last success. `#check`/`#print`/`#eval` queries run here too (not committed). `exact?`-style search tactics are committed as what they find. |
| `try{candidates}` | Test up to 8 candidate scripts **speculatively** from the current snapshot — cheap because snapshots are immutable, so every candidate is independent; the first that fully succeeds is committed (k ideas, one turn). |
| `auto_close{}` | Run the finisher portfolio (rfl, trivial, simp, omega, decide, norm_num, linarith, nlinarith, positivity, ring, field_simp+ring, simp_all, aesop, tauto, bound, gcongr, …) against the current goal, plus synthesized `nlinarith`/`positivity` hints and a final `exact?`; commits a closer if one makes progress. Cheap — call it freely. |
| `rollback{count}` | Undo the last N committed tactics and show the goal you are back to. O(1): drop snapshots from the list. |
| `state{}` | Re-render all open goals and the committed proof so far. |
| `verify{}` | Before declaring a project done: clean `lake build` at the project root, a `collectAxioms` audit of every declared constant (`sorryAx`, `Lean.ofReduceBool`, or under `LEAN_ENV_V2=1` any axiom outside `propext`/`Classical.choice`/`Quot.sound`), and a comment/string-aware scan of every `.lean` file for `sorry`/`admit`/`axiom`/`native_decide`. |

Cross-cutting enrichments (zero extra turns, default-on, `=0` disables):

- **error hints** (`LEAN_HINTS`) — rewrites Rocq/Coq-isms (`intros x.`,
  `lia`, `nra`, `destruct`, `assert`, `rewrite`, `Search`, `Qed`) and
  Lean 3-isms (`cases h with a b`, `rw h`, `λ x, e`, `{ }`) into Lean 4, and
  explains the common tactic failures (`linarith failed`, `omega could not
  prove`, `simp made no progress`, heartbeat timeouts) inline in the error.
- **did-you-mean** (`LEAN_SUGGEST`) — near-miss *existing* declaration names
  appended to unknown-identifier errors, ranked with `Lean.FuzzyMatching`
  (the same fuzzy scorer the language server's completion uses) over every
  constant in the session's own `Environment`, plus a shared-fragment and
  same-namespace bonus.
- **hint synthesis** (`LEAN_AUTO2`) — `auto_close` derives `sq_nonneg (x -
  y)`, `mul_pos hx hy`, `sq_nonneg (x ^ 3 - 1)` facts straight from the
  `MetaM` local context and goal of the current tactic state (arithmetic-typed
  hypotheses, `0 < _`/`0 ≤ _` hypotheses, even powers in the conclusion) — not
  from the printed goal string — and retries `nlinarith`/`positivity` with them.
- **tactic preloading** (`LEAN_PRELOAD`) — when the project depends on
  Mathlib but the file imports only part of it, the session adds
  `import Mathlib.Tactic` so the standard closers exist; on completion the
  response tells you the import line to add (`LEAN_IMPORT_ECHO`), and the
  written `candidate.lean` already carries it.
- **hang safety** — every tactic runs on an `IO.asTask` under a wall-clock
  budget (`LEAN_STEP_TIMEOUT`/`LEAN_TRY_TIMEOUT`/`LEAN_AUTO_TIMEOUT`/
  `LEAN_SEARCH_TIMEOUT`); on a miss the server sets an `IO.CancelToken` and
  simply stops waiting, reporting a structured TIMEOUT instead of freezing
  the session. Lean's own `maxHeartbeats` (kept at Lean's default, 200000 —
  not raised) is a second, deterministic guard. Honest caveat, measured in
  `docs/PHASE1_NOTES.md`: `Core.checkInterrupted` is purely cooperative,
  checked only between elaboration steps, so it cannot interrupt one opaque
  kernel reduction that never yields (e.g. a runaway `decide`) — the worker
  thread keeps running after the deadline; abandoning the wait is what keeps
  the *server* responsive, and process exit is what eventually reclaims it.
- **placeholder refusal** (unconditional, never gated by an env var) — a
  tactic unit whose PARSED syntax contains `sorry`, `sorryAx`, or `admit` is
  refused up front and never executed, in `step`/`try`/`check` alike: a
  `sorry` inside a comment or a string literal is untouched (neither ever
  reaches `Syntax`), but a nested `have h : P := by sorry` inside a longer
  unit is still caught. Separately, `import` is still refused up front only
  under `LEAN_ENV_V2=1`, mirroring rocq-mcp-evolve's `reject_require`
  (`ROCQ_ENV_V2=1`) — **off by default in both servers**. `native_decide`, an
  axiom injected via metaprogramming, etc. still execute like any other
  tactic, but a completion that depends on one of them is now caught
  in-session too, by the axiom audit below (2026-09-08, see "Verification").

## Verification: how a proof gets accepted, and how cheating is caught

**In-session completion audits what the proof term trusts, not just whether
one exists.** An earlier design made this deliberately shallow, matching
what was believed to be rocq-mcp-evolve's own behaviour: that server's
session accepts `Admitted.` exactly as it accepts a real `Qed.`, so — the
reasoning went — this server should accept `sorry`/`native_decide`/an
injected axiom in-session too, leaving all of it to the standalone gate
(below) to catch after the fact. **That parity claim was found FALSE on
2026-09-08**: the Rocq server's session completion means "a `Qed.` was
submitted and it succeeded" — `Qed.` FAILS outright after an `admit`, and
`Admitted.` (which *does* complete a Rocq "proof" the way this design let
`sorry` do) is a distinct vernacular command the tactic-running tools never
submit on the agent's behalf. There was never an in-session "placeholder
completes" behaviour on the Rocq side to have parity with. This server now
audits completions for real: `sorry`, an axiom injected mid-proof via
metaprogramming (`run_tac do Lean.addDecl (.axiomDecl ...)`), and
`native_decide` (which depends on the non-standard `Lean.ofReduceBool`
axiom) are all refused — `sorry` up front, before it can even execute; the
others at completion, via the axiom audit. The actual correctness arbiter
beyond that remains the standalone gate (`lake exe gate`, below), run by the
harness after the fact (or, for interactive use, opted into in-session via
`LEAN_GATE=1`) — it runs in a genuinely separate process and independently
re-derives everything from source, so it still catches classes of attack the
same-process in-session checks cannot (an "unchecked smuggle" that locally
overrides `debug.skipKernelTC` around a single `Lean.addDecl` call fools
`completionCheck`'s re-elaboration exactly as it fooled the live session,
since both run the same script in the same process — only a fresh process
that kernel-*replays* every locally-added constant catches it; see
`Tests.Session`'s A27).

### 1. In-session: `Driver.completionCheck` — goals closed, re-elaboration
clean, no `sorry`, axioms allowlisted

1. **No goals** — `tacticState.goals` is empty.
2. **Re-elaboration produces no errors** — the finished declaration
   (statement + committed script) is re-elaborated as a fresh command in the
   *prefix* state (`Lean.Elab.IO.processInput`), with `debug.skipKernelTC`
   forced **off** regardless of what the session itself was opened with (so
   the kernel actually re-checks the produced term, not just the
   elaborator's bookkeeping) — and this re-elaboration reports zero error
   messages.
3. **No `declaration uses 'sorry'` warning** on that re-elaboration
   (`isSorryWarningMsg`) — a second, independent backstop behind the
   up-front `sorry` refusal below (e.g. a tactic that manufactures a `sorry`
   term without the literal token).
4. **`Lean.collectAxioms` of the re-elaborated target ⊆ `{propext,
   Classical.choice, Quot.sound}`** — an injected custom axiom,
   `native_decide`'s `Lean.ofReduceBool`, etc. all fail this. `example`
   targets have no nameable constant to run this against (`example`
   elaborates under a transient internal name, `_example`, that is never
   added to the environment permanently); `completionCheck` splices the
   target's own `example` keyword into `theorem <synthetic name>` first
   (`spliceExampleKeyword`) so there is a real constant to look the axioms
   up under, and fails **closed** — not best-effort `true` — if that
   constant still can't be found afterward.

`getProofStatus` (REPL's own kernel-add + `hasSorry` check, ported from
`REPL/Main.lean`) stays defined in `Driver.lean` — the gate and the tests
still use it — but `completionCheck` does not call it: checks 3-4 above are
a strict superset of what it would add (an axiom allowlist has no analogue
in `getProofStatus` at all).

### 2. Up-front refusals — placeholder refusal (unconditional) +
`Session.rejectForbidden` (parity with rocq-mcp-evolve)

Two independent up-front refusals, on two different axes:

- **Placeholder refusal, restored 2026-09-08, never gated by an env var**:
  a tactic UNIT (one top-level tactic, as `step`/`try`/`check` already split
  the agent's text) whose PARSED syntax contains the atom `sorry` or the
  identifier `sorryAx`/`admit` is never executed. Decided on the unit's own
  parsed `Syntax` tree (adapted from `Gate.lean`'s own `forbiddenHits`
  walker), so a `sorry` hidden in a `--`/`/- -/` comment or inside a string
  literal never triggers it (neither ever makes it into `Syntax`), while a
  nested `have h : P := by sorry` inside a longer unit still does (the walk
  recurses into every subtree). In `step`/`check`, this follows
  commit-good-prefix exactly like a real tactic failure: earlier units in
  the same call stay committed, the offending unit is reported as an ERROR
  (`` `sorry` is not allowed: it closes the goal without a proof and an
  external checker rejects it — prove the goal or leave it open. ``), and
  nothing after it runs. In `try`, the whole candidate is reported as an
  error and never committed (no partial-commit concept within one
  candidate). The tool-call log's `stop` field reads `sorry_rejected` on
  this path (mirroring the `forbidden` field the `import` refusal below
  already logs).
- **`Session.rejectForbidden`, parity with rocq-mcp-evolve**: refuses
  exactly what rocq-mcp-evolve's own session server refuses, and nothing
  more — that server's `reject_require` refuses ONE thing, a `Require`
  command, detected on the **parsed** command, only when `ROCQ_ENV_V2=1`.
  This server mirrors that exactly: under `LEAN_ENV_V2=1`, the ONLY thing
  refused here is `import` — the literal Lean counterpart of `Require`
  (Lean has no mid-file import statement either, and the tactic modules a
  proof needs are already preloaded into the session, see `openFile`'s
  `withPreload`) — detected on comment/string-stripped text as a line whose
  first token is the keyword `import`, never by a raw substring match. With
  `LEAN_ENV_V2` unset (the default), this refusal is off — but the
  placeholder refusal above still applies regardless.

Everything else — `native_decide`, `run_tac`, an axiom injected via
metaprogramming, `set_option debug.skipKernelTC true`, ... — still
**executes** like any other tactic; none of it contains a literal
`sorry`/`sorryAx`/`admit` token for the placeholder refusal to catch. If it
closes the goal, §1's completion audit is what decides whether the result
counts — a disallowed axiom fails there now, but a same-process "unchecked
smuggle" (see the module intro above) can still fool it, which is what §3's
independent, separate-process gate is for. The `hint:` table (`Hints.lean`)
still advises against `sorry`/`admit` when it sees one used, exactly as the
Rocq server's hints do (it flags them as "FORBIDDEN — incomplete proofs are
rejected") — advice that now doubles as an explanation of a refusal that
already happened, rather than of one deferred to the grader.

### 3. The standalone gate: `lake exe gate`

```
gate <candidate.lean> --theorem <name> [--reference <reference.lean>] [--project <root>] [--json]
```

Prints `ACCEPTED` or `REJECTED: <reason>` and exits 0/1 (`--json` prints a
`{accepted, reason, target, axioms, unreplayed}` object instead). It is
**deliberately its own executable** (`GateMain.lean`, its own `lean_exe`, not
folded into the server binary): the whole reason it exists is that the
in-session checks above run in the *same process* as the agent's tactics, and
a tactic block that runs `run_tac`/`Lean.addDecl`/`Lean.Kernel.Environment.addDeclWithoutChecking`
can in principle corrupt or fool that process's own notion of "the
environment." The gate instead re-derives acceptance from nothing but the
candidate's source text, in a fresh process, in six steps, stopping at the
first rejection:

| # | step | rejection reason(s) |
|---|---|---|
| 1 | reference/statement tamper (only when `--reference` given): a byte-level comparison of everything outside the target's own proof against the reference, and the target's own statement text must be unchanged | `reference_unusable:<detail>`, `prefix_modified`, `statement_modified`, `suffix_modified` |
| 2 | forbidden tokens in the target's proof, decided on Lean's own parsed `Syntax` tree (`sorry`, `native_decide`, `run_tac`, `#eval`, `axiom`, `admit`, `addDecl`, `Lean.Elab`/`Lean.Meta`/`Lean.Environment` access, …) | `forbidden_token:<tok>` |
| 3 | a fresh compile of the whole candidate file (`Lean.Elab.IO.processInput`, `cmdState? := none`), scoped to the target's own line range | `compile_error:<msg>`, `sorry_warning` |
| 4 | the target is present, is not an `example`, and (when `--reference` is given) it compiles enough to produce the target constant and that constant's type matches the candidate's | `target_missing`, `target_is_example`, `reference_unusable:<detail>`, `statement_type_mismatch` |
| 5 | `Lean.collectAxioms` of the target ⊆ `{propext, Classical.choice, Quot.sound}` | `axiom:<name>` |
| 6 | **kernel replay**: every constant the candidate itself added is re-added through the KERNEL (never `addDeclWithoutChecking`) into a fresh environment built from the candidate's header imports only, via Lean core's own `Lean.Environment.replay` | `kernel_replay_failed:<name>:<msg>` |

Step 2 walks the parsed `Syntax` tree rather than scanning text, so a
`sorry`/`#eval` hidden behind a comment/string desync trick (a trailing line
comment followed by a bare block-comment opener, or a forbidden word inside a
string literal) can't hide or fake a hit either way — comments never make it
into `Syntax`, and a genuine parse failure from such a trick is instead
caught by step 3's fresh compile. Step 6 uses Lean core's `Environment.replay`
(`Lean/Replay.lean`) rather than a hand-rolled topological sort: it already
threads dependencies in the right order and calls the kernel
(`addDeclCore`, `doCheck := true`) for every constant; `Gate.lean`'s
`Replay` namespace is that same algorithm adapted, with attribution, to tag a
kernel rejection with the failing constant's name (`Environment.replay`
itself discards it once it throws).

**Step 1 is a byte-level comparison, not a declaration-level one.** Given a
target declaration `d`, let `before(src) = src[0 : d.stmtEndPos]` (everything
up to, but not including, the target's own `:=`) and `after(src) = src[d.endPos:]`
(everything after the target). The candidate is accepted at this step only if
its statement text matches the reference's exactly (else `statement_modified`,
checked first), `before(candidate) == before(reference)` — tolerating exactly
one extra `import Mathlib.Tactic` header line the candidate has and the
reference doesn't (else `prefix_modified`) — and `after(candidate) ==
after(reference)` (else `suffix_modified`). Comparing raw bytes outside the
proof region, rather than comparing only the declarations `Text.findDecls`
locates, means a smuggled top-level command that is *not itself a
declaration* — `set_option debug.skipKernelTC true`, `variable (h : False)`,
`open .. in`, `macro_rules`, `notation`, a bare `#eval <arbitrary IO>` —
cannot slip in unnoticed between/around declarations the way it could when
only declaration texts were diffed. Regression: D12 in `Tests/Gate.lean`.

**Step 3's compile-error/sorry-warning check is scoped to the target's own
line range** `[startLine+1, endLine+1]` (`Message.pos.line` is 1-based;
`Text.Decl.startLine`/`endLine` are 0-based), not the whole file. A task file
routinely carries other holes — other `sorry` theorems, or an earlier broken
proof Lean still admits with an error — and none of that is the candidate's
doing to fix; only a message positioned inside the target's own declaration
counts. This is sound rather than a loophole because (a) with `--reference`,
everything outside the target's proof region is byte-identical to the
reference (step 1 above), so a pre-existing hole elsewhere was already there
and isn't something the candidate introduced, and (b) any dependency of the
target itself on a sorried/broken declaration still surfaces as `sorryAx` in
`Lean.collectAxioms` (step 5), and every local declaration the candidate
added is kernel-replayed (step 6) regardless of which declaration it is —
so a target that only *looks* clean because it leans on a hole elsewhere is
still caught, just by a later step. Regression: D11 in `Tests/Gate.lean`.

**Step 4 fails closed when the reference itself is unusable for
comparison.** `reference_unusable:<detail>` covers: the `--reference` path
doesn't exist or can't be read, the reference has no declaration under the
requested name at all (step 1's own textual lookup), the reference fails to
compile outright, or the target name is absent from the reference's compiled
environment. None of these are treated as "no reference given, skip the type
check" any more — a `--reference` flag that can't actually be used for
comparison is a configuration error, not permission to skip step 4.
Regression: D10 in `Tests/Gate.lean`. The type-comparison fallback itself
(when plain `Expr` equality fails) now pretty-prints both sides with
`pp.all true` — fully explicit, implicits/universes shown — before comparing
strings, closing the gap where two genuinely different types could
pretty-print identically under default (elided-implicit) settings.

**`LEAN_GATE=1` is a Lean-only convenience, off by default, NOT part of the
Rocq protocol** — rocq-mcp-evolve's session server never calls its gate
in-session at all; `harness/gate.py` is only ever run by the surrounding
benchmark harness, after the fact, against whatever the agent's transcript
ends on. This server exposes the *same* out-of-process gate as an optional
in-session hook purely for interactive convenience (so an agent working at a
terminal can be told the truth immediately rather than only at benchmark
time): set `LEAN_GATE=1` and, on every proof completion, `Session.completeMsg`
writes `candidate.lean`, then runs the gate against it before telling the
agent PROOF COMPLETE. **Fail-closed by design**: the only fail-*open* case is
`LEAN_GATE` unset (the default) — the hook is then simply not consulted, as
if it didn't exist, exactly matching the Rocq protocol's own default. Once
enabled, a clean exit 0 with `ACCEPTED` on stdout is the *only* accepting
outcome; the binary missing, a non-zero exit without a `REJECTED:` line, a
timeout, or malformed output are all treated as a rejection with reason
`gate_unavailable:<detail>` — using the exact same response shape as a real
`REJECTED: <reason>`, so a misconfigured or broken gate is visible to the
agent, not silently bypassed. On any rejection the last committed unit is
rolled back (`complete` becomes `false` again) and the just-written
`candidate.lean` is deleted, so no file is left on disk claiming a proof
that didn't actually pass.

### Residual risks (honest accounting)

- **Trust boundary**: the gate trusts the Lean binary itself and the
  imported `.olean`s of the project it runs against — a tampered dependency
  `.olean` (as opposed to tampered source text) is out of scope, exactly as
  for the Rocq gate this ports (see `docs/DESIGN.md`).
- **`example` targets cannot be gated**: step 4 rejects them outright
  (`target_is_example`) since an anonymous declaration has no constant to
  look up axioms/replay for at the top level — use a named `theorem`.
- **Reference comparison is partial, not full semantic equivalence**: step 1
  is a byte-level diff of everything outside the target's own proof (see
  above) — genuine textual identity, not semantic equivalence, so a reference
  and candidate that differ only in, say, whitespace inside a *preceding*
  declaration still trip `prefix_modified`; step 4's type check is an
  `Expr`-level comparison of the target's *type* only (alpha-equivalence
  first, falling back to comparing `pp.all true` pretty-printed strings for
  the universe-parameter-naming corner case) — the proof *term* itself is
  never compared against a reference proof, only kernel-checked on its own
  merits.
- **The `blankMathlibImportLine` limitation**: to locate the target's proof
  syntax for step 2 in a project without Mathlib, the gate blanks out a
  literal `import Mathlib.Tactic` header line (space-padded, so positions
  after it are unaffected) purely for parsing — the real compile (step 3)
  and the kernel-replay base environment (step 6) always use the untouched
  source. If the target's proof text relies on genuinely new *syntax*
  `Mathlib.Tactic` introduces (not just tactics/lemmas resolved during
  elaboration), the blanked-header parse can still fail to locate the proof;
  when that happens the forbidden-token check passes *conservatively*
  (`none` found), relying on steps 3–6 for safety instead. Regression: D9 in
  `Tests/Gate.lean`.
- **Unsafe/partial constants are not kernel-replayed**: `replayNamed` skips
  any constant marked `unsafe` or `partial` (the kernel has nothing to check
  for them); the gate's verdict records their names in `unreplayed` rather
  than silently dropping them, but `unsafe` is itself always a forbidden
  token (step 2), so a candidate proof cannot introduce one directly.
- **Step 1 only runs with `--reference`**: without one, the gate never
  checks whether the statement itself was weakened relative to the original
  task — it only validates the proof of whatever statement the candidate
  file declares under the given name.
- **The gate elaborates the candidate in its own process**: step 3's fresh
  compile executes whatever Lean metaprograms the candidate's *whole file*
  contains — not just the target's proof — in the gate's own process, before
  the forbidden-token check (step 2, target-scoped) or anything else has a
  chance to object to what happens outside the target. With `--reference`,
  the executed text outside the target's proof region is byte-identical to
  the reference (step 1 above), and inside the proof region the token check
  forbids the known escape hatches (`run_tac`, `#eval`, `set_option`,
  `addDecl`, …) before step 3 ever runs. But this is still trust placed in
  the reference file and in the completeness of the forbidden-token
  allowlist, not a sandbox: for adversarial settings (untrusted candidates,
  no controlled reference), run the gate itself inside a sandbox/container
  rather than relying on the token check alone.
- **Kernel replay is in-process, not independently re-verified**: step 6
  replays every constant through the same in-process kernel implementation
  (`Lean.Kernel.Environment.addDeclCore`) that elaborated the file in the
  first place — a bug or compromise in that one kernel binary is not caught
  by anything in this pipeline. An independent kernel re-check with
  [`lean4checker`](https://github.com/leanprover/lean4checker) (a
  second, separately-built kernel implementation) on the produced
  environment is the natural next assurance step beyond what `Gate.lean`
  does today.

## Install & try (2 minutes)

The server can only load `.olean`s built by the same Lean version as your
project — the same constraint as the REPL, Pantograph or LeanDojo. Build it
with **your project's toolchain** (this repo's `lean-toolchain` currently
pins `leanprover/lean4:v4.27.0-rc1`; if your project uses a different Lean
4 version, edit `lean-toolchain` and `lakefile.toml`'s `repl` `rev` to match
before building):

```sh
git clone <this repository>
cd <this repository>/lean-experiment
lake build
```

Then add ONE block to any MCP client config (Claude Code, `claude` CLI,
Cursor, or anything MCP-speaking), pointing at the built binary run through
`lake env` from this checkout (so `LEAN_PATH` resolves the `repl` dependency):

```json
{
  "mcpServers": {
    "lean": {
      "command": "lake",
      "args": ["env", "/absolute/path/to/lean-mcp-evolve/.lake/build/bin/lean-mcp-evolve"],
      "cwd": "/absolute/path/to/lean-mcp-evolve"
    }
  }
}
```

Running the binary directly (without `lake env`) also works when the project
is known at launch (`LEAN_PROJECT_ROOT`, or a `LEAN_TASK_FILE` preset inside a
Lake project): if `LEAN_PATH` is not already set, the binary re-executes itself
as `lake env <self>` from that project root (`LeanMcpEvolve/Reexec.lean`; the
`gate` executable does the same from `--project` or the candidate's project),
so `LEAN_PATH`/`LEAN_SYSROOT` come from the project's own toolchain. Setting
the search path programmatically is not enough — the REPL's `processInput`
re-reads it from the environment, and outside a project tree elan resolves the
*default* toolchain — which is why the bootstrap exists (2026-09-06,
`testing/README.md` "Resolved issue"). For interactive use without a preset,
launch through `lake env` as shown above, or export `LEAN_PATH` yourself.
`LEAN_NO_REEXEC=1` disables the bootstrap.

That's it. Ask your agent to finish a proof: it calls `open{file}`
(optionally `theorem:<name>` to target a `sorry` or any statement mid-file),
works the proof with the other tools, and on completion receives the
finished declaration to paste into the file (also written to
`LEAN_WORKDIR/candidate.lean` as the whole file with the proof spliced in).

**The default configuration — no environment variables at all — is the Rocq
server's own default**: all nine tools and every enrichment (hints,
did-you-mean, hint synthesis, tactic preloading, import echo) on; nothing
refused up front (`LEAN_ENV_V2` off, exactly like `ROCQ_ENV_V2`); in-session
completion means "the goal is closed and the declaration elaborates," so
`sorry` (or anything else that closes the goal) is reported PROOF COMPLETE
with `candidate.lean` written; and no in-session gate (`LEAN_GATE` off) —
correctness is whatever the harness decides by running `lake exe gate`
afterwards, exactly as the Rocq benchmark decides correctness by running its
own gate against the transcript, not by anything the session itself enforced.
`LEAN_ENV_V2=1` and `LEAN_GATE=1` are the two harness knobs this server
adds: the former mirrors `ROCQ_ENV_V2` bit-for-bit (see "Verification"
above); the latter has no Rocq equivalent — it is a Lean-only convenience
that runs the same standalone gate in-session, for interactive use, instead
of only after the fact (see "Verification" above).

Everything else is automatic:

- **Project discovery** — the server walks up from the opened file to the
  nearest `lakefile.lean`/`lakefile.toml` and treats that as the project
  root for search-path discovery and relative paths (`LEAN_PROJECT_ROOT`
  overrides). Build the target project first (`lake build`, and
  `lake exe cache get` for a Mathlib project) so its imports resolve.
- `LEAN_TASK_FILE` (optional) presets a file at launch — used by a benchmark
  harness; interactive use never needs it. `LEAN_LOG_FILE`/`LEAN_LOG_META`
  append one JSONL record per tool call for instrumentation.

Quick smoke without any MCP client:

```sh
printf '%s\n%s\n%s\n' \
  '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}' \
  '{"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"open","arguments":{"file":"/path/to/Project/File.lean","theorem":"my_sorry_lemma"}}}' \
  '{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"auto_close","arguments":{}}}' \
  | lake env /absolute/path/to/lean-mcp-evolve/.lake/build/bin/lean-mcp-evolve
```

## Excluding Mathlib import time from attempt budgets

`import Mathlib` costs 7–120s (cold page cache: tens of seconds; warm: single
digits) **per Lean process**, and — for a benchmark harness driving many
attempts, each with its own hard wall-clock deadline like
rocq-mcp-evolve's `run_eval.py` — that cost is not part of what any model
attempt should be charged for. This server (1) pays the import as rarely as
possible per process, (2) pays it *before* the model's first tool call
whenever the task file is already known, and (3) reports exactly how long
each import took, in machine-readable form, so the harness can subtract it
from the deadline it enforces.

**1. One header load per distinct import list, ever.** `open`/`build`
(and `diagnoseFile`'s use inside `open`'s own default-target selection)
split header processing (`import ...` lines only) from the rest of a file's
commands: the header alone is compiled once per *distinct, order-normalised
import list* per process (`Driver.getHeaderState`/`headerCache`), and every
file/target that needs the same imports — including the `import
Mathlib.Tactic` line `open` injects when a project has Mathlib and the file
doesn't already import it, which is its own, separately-cached, import list —
reuses that `Command.State` instead of re-running `import Mathlib`. A second
file with the same imports opened right after the first pays essentially
nothing for its header (see suite A32/M7 below).

**2. Prewarm: start the import before the model's first turn.** When
`LEAN_TASK_FILE` is set (harness mode) or `LEAN_PREWARM_IMPORTS` is set (a
comma-separated module list, e.g. `Mathlib` — an explicit override, used when
the harness knows what's needed before it knows the exact task file, or
instead of guessing from one), the server starts loading that header
environment in a background task **immediately at startup, before the MCP
`initialize` handshake is answered** — the handshake itself returns in
milliseconds; the import runs concurrently on its own dedicated thread.
`open` (explicit, or the lazy `LEAN_TASK_FILE` open triggered by the first
tool call) waits for this background task only when its own needed import
list matches exactly; otherwise it imports normally, so a prewarm guess that
turns out wrong never blocks on the wrong header, it just misses the cache
like any other request would. This is layered under the existing
`LEAN_EAGER_OPEN` mechanism, which starts the FULL `open` (header + prefix +
statement elaboration) for a `LEAN_TASK_FILE` preset in the background the
same way — the two never pay the same import twice, since the eager open's
own header fetch waits on/hits the prewarm task's cache entry instead of
redoing the work. `LEAN_PREWARM=0` disables prewarm (both triggers);
`LEAN_EAGER_OPEN=0` independently disables the full eager open.

**3. Every header load is accounted for, in the JSONL log
(`LEAN_LOG_FILE`).** One record per header load — cache hit or miss, prewarm
task or request-triggered:

```json
{"seq": 7, "ts": 1799999999.1, "kind": "import", "modules": ["Mathlib"], "dur_ms": 41230.4, "cached": false, "prewarm": true}
{"seq": 12, "ts": 1800000003.4, "kind": "import", "modules": ["Mathlib"], "dur_ms": 0.0, "cached": true, "prewarm": false}
```

`modules` is the sorted, deduplicated import list; `dur_ms` is that record's
own wall time (≈0 on a cache hit); `cached` says whether this call found the
header already materialized; `prewarm` says whether this call went through
the background-prewarm-task path (waited on it, or *was* it).

In addition, every `tool_call` log record carries `import_ms`: the wall time
THAT call's handling spent on imports — a cache miss it triggered directly,
or a background prewarm task it had to wait for mid-call (both complete
strictly within the call's own `[t0, t1]` window, so a running process-wide
counter's delta over that window captures it exactly). `open`'s `tool_call`
record additionally carries `import_cached` (whether ITS header was a cache
hit). On exit (`onExit`, i.e. on stdin EOF / process shutdown) the server
appends one `{"kind": "shutdown", "import_ms_total": ...}` record with the
process-wide running total of all header-load time, cached or not:

```json
{"seq": 40, "kind": "shutdown", "ts": 1800000100.0, "import_ms_total": 41230.4}
```

**Harness recipe.** Read the server's JSONL log while the attempt runs (or
just once at the end):

- (a) **Extend the kill deadline** by each `import` record's `dur_ms` as it
  appears — an attempt that happens to trigger a real `import Mathlib` (a
  cache miss, or the very first request of a fresh process with no prewarm)
  should not be charged for it.
- (b) **Report `wall_s - import_s`** (wall time minus the sum of every
  `import` record's `dur_ms` observed during the attempt, in seconds) as the
  attempt's *effective* wall time, instead of raw wall-clock.

With prewarm enabled (the default whenever `LEAN_TASK_FILE`/
`LEAN_PREWARM_IMPORTS` is set), the import overlaps the client's own startup
and the model's first turn — by the time the model's first tool call lands,
the header is very often already cached, so most of `import Mathlib`'s cost
never touches the budget at all, and (a)/(b) above become a small correction
rather than the dominant term.

## Configuration reference

| variable | default | meaning |
|---|---|---|
| `LEAN_ENABLE_TOOLS` | all nine | comma-separated subset to expose |
| `LEAN_HINTS`, `LEAN_SUGGEST`, `LEAN_AUTO2`, `LEAN_PRELOAD`, `LEAN_IMPORT_ECHO`, `LEAN_AUTO_SEARCH` | on | `=0` disables the enrichment (`AUTO_SEARCH` = the `exact?` closer in `auto_close`) |
| `LEAN_STEP_TIMEOUT` / `LEAN_TRY_TIMEOUT` / `LEAN_AUTO_TIMEOUT` / `LEAN_SEARCH_TIMEOUT` | 30 / 15 / 6 / 25 s | wall-clock budget per round (step & check / try candidate / auto_close closer / `exact?`); the Rocq server's own equivalents default lower — `step`/`check` 10 s, `try` 5 s, `auto_close` 2 s per candidate — Lean tactics (`ring`, `nlinarith`, `decide`) are typically slower per call than their Rocq counterparts, hence the wider budgets here |
| `LEAN_OPEN_TIMEOUT` / `LEAN_BUILD_TIMEOUT` | 600 / 600 s | file prefix load / whole-file diagnosis and `lake build` |
| `LEAN_MAX_HEARTBEATS` | 200000 | Lean's own per-tactic heartbeat cap (user-facing units, ×1000 internally); deliberately **not** raised beyond Lean's default — see "hang safety" above |
| `LEAN_PROJECT_ROOT` | discovered | project root for relative paths and `verify` |
| `LEAN_WORKDIR` | temp dir | where `candidate.lean` is written on completion |
| `LEAN_PORTFOLIO_EXTRA` | — | newline-separated extra finishers for `auto_close` |
| `LEAN_ENV_V2` | off | `=1` refuses `import` up front — the ONLY up-front refusal, bit-for-bit parity with rocq-mcp-evolve's `ROCQ_ENV_V2`/`reject_require` (`Require`); a harness knob, off by default exactly like `ROCQ_ENV_V2` — the default configuration refuses nothing |
| `LEAN_GATE` | off | `=1` enables the out-of-process correctness gate in-session, on every completion (fail-closed once set — see "Verification" above). Lean-only: has no Rocq equivalent (the Rocq protocol runs its gate only from the surrounding harness, never in-session) — off by default, matching the Rocq protocol's own "no in-session gate" default |
| `LEAN_GATE_BIN` | `<dir of the running server binary>/gate` | override the path to the `gate` executable |
| `LEAN_TASK_FILE`, `LEAN_LOG_FILE`, `LEAN_LOG_META` | — | harness knobs (see above); `LEAN_TASK_FILE`, when set, is also passed to the gate as `--reference` |
| `LEAN_EAGER_OPEN` | on | `=0` disables starting the FULL `open` of a `LEAN_TASK_FILE` preset in the background at launch (see "Excluding Mathlib import time from attempt budgets") |
| `LEAN_PREWARM` | on | `=0` disables the header-only background prewarm (both `LEAN_TASK_FILE`- and `LEAN_PREWARM_IMPORTS`-triggered) — see "Excluding Mathlib import time from attempt budgets" |
| `LEAN_PREWARM_IMPORTS` | — | comma-separated module list (e.g. `Mathlib`) to prewarm at launch instead of (or in addition to) guessing from `LEAN_TASK_FILE`; explicit, takes priority when both are set |
| `LEAN_MCP_DEBUG=1` | — | driver trace on stderr (stdout carries only JSON-RPC) |

JSONL log fields added by the import-timing deliverable (see above for full
record shapes): `kind: "import"` records (`modules`, `dur_ms`, `cached`,
`prewarm`); every `kind: "tool_call"` record's `import_ms`; `open`'s
`tool_call` record's additional `import_cached`; and the `kind: "shutdown"`
record (`import_ms_total`) emitted once on exit.

## Tests

`lake exe tests` (from this checkout, after `lake build`) — spawns the real
built server over MCP stdio for suite A, and the built `gate` executable as a
subprocess for suite D; T is pure in-process unit checks. Suites T, A and D
run under `lake exe tests` (M is manual, see below). Pass a suite letter to
run just one: `lake exe tests A`.
Architecture: [`Tests/ARCHITECTURE.md`](Tests/ARCHITECTURE.md).

- **T** (`Tests/Text.lean`, 12 cases, 35 checks) — the pure text layer:
  parser-driven declaration location, statement/proof split, tactic-unit
  splitting, comment/string-aware forbidden scan (incl. the Rocq D4 desync
  exploit), `Try this:` parsing, import scanning, truncation.
- **A** (`Tests/Session.lean`, 32 cases, 221 checks) — session contracts on a
  dependency-free core project built on the fly: commit-good-prefix,
  auto-complete handshake, `try` semantics, `auto_close` progress rule,
  rollback + query non-commit, unconditional placeholder refusal (a bare
  `sorry`, a nested `have h : P := by sorry`, `sorryAx` spelled directly,
  a commented-out/string-literal `sorry` NOT refused — A7/A7b/A24), hints +
  did-you-mean, whole-proof `check`, runtime `open` (first-unproven default,
  named theorem, reach past broken proofs), `build`, `verify`, timeout
  safety, `exact?` splicing, instrumentation, in-session axiom-injection/
  `example` completion (A21–A25, see below), and the standalone gate's
  residual value beyond the in-session checks (an unchecked `addDecl`
  smuggle only kernel replay catches, A27).
- **D** (`Tests/Gate.lean`, 12 cases D1–D12, 49 checks) — the out-of-process
  correctness gate (`lake exe gate`), run as a real subprocess for the
  CLI-level cases and in-process for the "defense in depth" cases that
  disable the forbidden-token check to prove steps 3–6 independently reject
  what step 2 would already have caught: legit accept, placeholder rejection,
  statement/prefix tamper, the Rocq D4 comment/string desync exploit,
  `native_decide`'s hidden axiom, an injected axiom via `run_tac`, an
  unchecked `addDecl` smuggle caught only by kernel replay, a missing
  target, the one tolerated header addition (a bare `import
  Mathlib.Tactic` line on a project without Mathlib), an unusable
  `--reference` (missing/wrong-name, D10), target-scoped compile
  errors/sorry warnings on a multi-hole task file (D11), and the byte-level
  tamper check catching a smuggled non-declaration command such as
  `set_option`/`variable`/`#eval` (D12). See
  [`Tests/ARCHITECTURE.md`](Tests/ARCHITECTURE.md) for the case-by-case
  breakdown.
- **M** (`Tests/Mathlib.lean`, 5 cases M1–M5, 29 checks) — Mathlib-backed:
  hint synthesis closes the `(x^6+1)/2 ≥ x^3` goal, Rocq-isms at a real
  goal, preloading + import echo, `exact?` inside a bullet, `build` on a
  Mathlib file. Skipped automatically unless
  `LEAN_MCP_TEST_MATHLIB_PROJECT=<built project depending on Mathlib>` is
  set — this suite is run manually against a local Mathlib checkout, not in
  CI (see `.github/workflows/ci.yml`), because it needs a project with
  Mathlib already built (tens of minutes).

## Repo map

```
LeanMcpEvolve/
  Mcp.lean      MCP stdio server: newline-delimited JSON-RPC 2.0, tool registry, JSONL instrumentation
  Proc.lean     spawn a process with a hard timeout, capture combined output, kill on timeout (used by verify's lake build)
  Text.lean     declaration location via Lean's own parser, statement/proof split, tactic-unit splitting, forbidden-token scan
  Driver.lean   the session engine on REPL snapshots: prefix processing, proof snapshot from `sorry`, run units with timeout+heartbeats, error classification, goal rendering, completion check, whole-file diagnosis, fuzzy did-you-mean
  Hints.lean    error-hint table (Rocq/Coq-isms, Lean 3-isms, message-keyed), hint-term synthesis for nlinarith/positivity
  Verify.lean   lake build + axiom audit (collectAxioms) + forbidden-token scan
  Session.lean  the nine tools (handlers, schemas, response texts); rejectForbidden, the LEAN_GATE hook (runGateCheck/completeMsg)
  Gate.lean     the out-of-process correctness gate: 6-step pipeline (tamper, forbidden tokens, fresh compile, target/type, axioms, kernel replay via Lean.Environment.replay)
  GateMain.lean the `gate` executable's entry point (its own lean_exe, separate process from the server)
  Main.lean     entry point: parse LEAN_ENABLE_TOOLS, run the MCP loop
Tests/
  Helpers.lean  spawn-the-server / JSON-RPC / core-project mini-lib
  Text.lean     suite T
  Session.lean  suite A
  Gate.lean     suite D (the correctness gate, D1-D12)
  Mathlib.lean  suite M
  Fixtures/     F1.lean, F2.lean, F3.lean, Build.lean
  Main.lean     `lake exe tests` entry point
docs/DESIGN.md  Rocq → Lean mapping of every design decision
docs/PLAN.md    the implementation plan this server was built from
```

## Relationship to other Lean agent tooling

[lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) exposes the language
server's *inspection* surface (goals at positions, hover, diagnostics,
completions, external searches) as many small tools. This server keeps the
Rocq experiment's *proof-session* surface instead — a committed script with
speculative evaluation, a portfolio closer and push-based enrichments —
because that is what the ablations found to move pass@1 and cost. The two
are complementary and can be attached side by side.

This server depends on the [Lean REPL](https://github.com/leanprover-community/repl)
library (`leanprover-community/repl`, pinned via `lakefile.toml`'s `require`
to the git tag matching this project's toolchain) for the immutable
`ProofSnapshot` primitive that makes O(1) rollback and independent
speculation possible — the same primitive the REPL itself exposes to
external tools over its own line protocol, and that Pantograph/LeanDojo
build similar snapshot-based interfaces on top of.

License: Apache-2.0 (as the original).
