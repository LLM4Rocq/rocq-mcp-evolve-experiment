# Frozen configuration — Lean port

(ported from rocq-mcp-evolve's `configs/FROZEN.md`, with Lean values)

**Config**: `configs/frozen.json` = the direct Lean analogue of
rocq-mcp-evolve's frozen winner (`session_try_hints_auto_sugg` + environment
v2). Interface: the `lean-mcp-evolve` in-process session server, tools
`step` / `rollback` / `state` / `try` / `auto_close` (Lean-ism hints,
did-you-mean suggestions, all of Mathlib always available, `import`
refused). See `testing/README.md`'s arm table for the full 12-config matrix
and the Rocq arm each mirrors.

**Policy (fixed)**: `claude-haiku-4-5` via `claude` CLI headless, MCP tools
only, ≤30 turns, ≤300s wall per attempt, parallel=4 (pf arms ≤100 turns,
parallel=8; opus arms 1 rep — see the arm table). On this machine the
parallelism is capped at 1 by memory (12-16 GB per Mathlib-loaded process) (README deviation 15); budgets per
attempt are unchanged.

**Substrate**: Lean 4 `v4.27.0-rc1`, Mathlib pinned by
`/Users/jviennot/Documents/Cours/LEAN_2026`'s `lake-manifest.json` (override
via `LEAN_EVAL_PROJECT`). elan toolchain binaries at `~/.elan/bin`.

**Frozen at**: the target repo is not a git repository (PORT_SPEC.md); the
closest available provenance signal is a sha256 of the built
`.lake/build/bin/lean-mcp-evolve` binary, recorded in every run's
`run_meta.json` as `binary_sha256_lean_mcp_evolve` (see Deviations #6 in
`testing/README.md`). Before the held-out run, record that hash here once
computed:

```sh
shasum -a 256 .lake/build/bin/lean-mcp-evolve
```

## Held-out procedure (run exactly once, after this file reflects the frozen binary hash)

1. `touch testing/FINAL_UNLOCK` at the repo root (mechanical guard; the
   unlock is logged to `testing/logs/unlock.log` by `harness/datasets.py`).
2. Generate the putnam60 manifest at unlock time (the guard makes this the
   first moment the full 60-problem manifest can be assembled):
   `LEAN_FINAL_EVAL=1 python3 testing/harness/make_putnam_manifest.py`
3. Run every one of the 12 arms, 2 reps each (opus arms 1 rep) for
   pass@1/pass@2, per the launch commands in `testing/README.md`. Arms run
   SEQUENTIALLY for wall-clock integrity (mirrors rocq-mcp-evolve's
   sequential-arm convention for its own 6-arm final matrix).
4. Report via `python3 testing/harness/final_tables.py`; no reruns, no
   tuning, no second look. Sleep-contaminated attempts (`machine_slept`) are
   the sole permitted repair (redo of the identical slot via
   `harness/repair_run.py`), per the pre-registered protocol rocq-mcp-evolve
   used.

## Anti-gaming gate (see testing/README.md's gate mapping table)

Locked prefix (whitespace-normalized) · forbidden-token region scan (Lean's
own, longer, list) · fresh-dir recompile via the built `gate` binary,
STRICTER byte-level prefix/suffix/statement lock against `--reference` ·
axiom audit · kernel replay. Rejection reasons logged verbatim in
`results.jsonl`'s `reject_reason` / `gate` fields.

**Pre-condition (satisfied 2026-09-06)**: the `gate` and `lean-mcp-evolve`
binaries must be built with the `lake env` bootstrap (`LeanMcpEvolve/Reexec.lean`);
without it, binaries launched by `run_eval.py` cannot resolve `import Mathlib`
(see `testing/README.md`, "Resolved issue"). `test/test_gate.py` must pass 8/8
before the unlock.

## Arm matrix (section 4/8 of PORT_SPEC.md, FINAL_ run ids)

Twelve arms, `FINAL_<config_id>`, expected n = 120 (60 problems × 2 reps;
opus arms n = 60, 1 rep) — see `harness/final_tables.py`'s `ARMS` list,
which REFUSES to emit a table until every arm's integrity gates pass (row
counts, zero live quota-poisoning markers, zero `machine_slept`, and — for
every arm except `FINAL_frozen`, the phase-1 haiku exemption mirroring
rocq-mcp-evolve's own — zero turn-cap-terminated rows).
