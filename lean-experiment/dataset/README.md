# PutnamBench evaluation subset (60 problems, 3 tiers)

## Purpose

A 60-problem subset of PutnamBench Lean 4 statements, split into three
20-problem difficulty tiers (`easy`, `medium`, `hard`), for evaluating LLM
agents that drive Lean 4 through the `lean-mcp-evolve` MCP server. The tiers
are calibrated against the PutnamBench leaderboard: `easy` problems are
solved by essentially every prover class, `medium` problems separate
2025-generation agentic systems from earlier single-shot/small-search
provers, and `hard` problems remain (mostly) unsolved even by the strongest
systems on the leaderboard.

Each problem is a self-contained Lean file with a `theorem ... := sorry`
statement, taken verbatim from PutnamBench with any numerical answer
inlined into the statement (see "Provenance" below), so an agent only has
to close the final `sorry`.

## Provenance

- Source: [PutnamBench](https://github.com/trishullab/PutnamBench), commit
  `59056d63eebbd01b921945b145182fcf97ec3ac0`, directory `lean4/src`.
- Toolchain: Lean `v4.27.0` (`lean4/lean-toolchain`), Mathlib `v4.27.0`
  (`lean4/lakefile.lean` pins `require mathlib ... @ "v4.27.0"`, resolving to
  mathlib4 commit `a3a10db0e9d66acbebf76c5e6a135066525ac900`).
- Variant: "with-solution" (`lean-wsolution` in the leaderboard), i.e. every
  problem that asks for a value/function/set as an answer has that answer
  substituted for the `abbrev ..._solution := sorry` placeholder, using
  PutnamBench's own `lean4/scripts/rewrite_solutions.py` (copied here as
  `scripts/rewrite_solutions.py`, unmodified). This is the variant the
  leaderboard's "lean-wsolution" column reports against, and it is the
  variant used throughout the selection methodology below (all `nw`/`nm`/`ns`
  counts are `lean-wsolution` counts). 346 of the 672 PutnamBench Lean
  problems have such an answer; 32 of the 60 selected problems do (`easy`
  15/20, `medium` 6/20, `hard` 11/20) — `manifest.json`'s `has_answer` field
  records, for every selected problem, whether the *original* (answer-free)
  file contained an `abbrev ..._solution`.
- Informal statements/solutions and tags: `PutnamBench/informal/putnam.json`
  (used with permission from the MAA, see "License" below).
- Leaderboard data: `PutnamBench/docs/results.json`, fetched from the live
  PutnamBench leaderboard.

### How to regenerate

1. Check out PutnamBench at the commit above (or a later one, if the
   selection is intentionally being refreshed) next to this repo.
2. Run `scripts/rewrite_solutions.py` from inside the PutnamBench checkout's
   `lean4/` directory to produce `solutions_replaced_new/*_sol.lean`; these
   are the "with-solution" files (the ones copied into `easy/`, `medium/`,
   `hard/` here, minus the `_sol` suffix and any files not in the selection).
3. From a directory containing that PutnamBench checkout, run in order:
   - `scripts/parse_lb.py` — parses `docs/results.json`'s free-text `note`
     fields into per-approach solved-problem-id sets (`solved.json`) and
     per-approach metadata (`meta.json`).
   - `scripts/score.py` — assigns each of the 672 Lean problems its
     `weak`/`mid`/`strong` solver lists and `nw`/`nm`/`ns` counts
     (`scores.json`), using the fixed WEAK/MID/STRONG approach-name lists
     documented below.
   - `scripts/select.py` — computes the `easy` ranking and the `medium`/
     `hard` candidate pools (`pools.json`).
   - `scripts/finalize.py` — applies the hand-picks and stratification
     described below to produce the final 60-problem `selection.json`.
4. Copy the selected `_sol.lean` files into `easy/`, `medium/`, `hard/` per
   `selection.json`, and rebuild `manifest.json`/`manifest.csv` from
   `selection.json`, `scores.json`, `solved.json`, `filehist.json`, and
   `informal/putnam.json`.

Re-running this against a newer PutnamBench/leaderboard snapshot will not
reproduce the same 60 problems exactly, because the leaderboard grows over
time (see "Caveats").

## Methodology

**1. Universe.** All 672 PutnamBench Lean 4 problems, minus the 12 from
year 2025 (660 remain), because several of the mid-tier systems used to
define the `medium` tier only evaluated on years ≤ 2024; leaving 2025 in
would make some 2025 problems look artificially unsolved by those systems
(they were simply never attempted). Concretely, restricting to year ≤ 2024
leaves the medium candidate pool unchanged at 145 (no 2025 problem
qualified) but changes the hard candidate pool from 58 to
the intended 54 (4 of the year-2025 problems would otherwise have
qualified).

**2. Approach tiers**, built from each leaderboard entry's free-text `note`
field (parsed by `scripts/parse_lb.py` into a per-approach set of solved
problem ids) and classified by hand into three bands. See the tables below
for links and solved counts.

- **WEAK** — small provers and single-shot/moderate-search LLMs (pass@k up
  to ~1000): GPT-4o, COPRA (GPT-4o), Deepseek R1, Goedel-Prover-SFT, ABEL,
  InternLM2.5-StepProver, Self-play Theorem Prover,
  gemini-2.0-flash-thinking-121, gemini-2.5-pro-exp-0325,
  Kimina-Prover-7B-Distill, o4-mini-high, DeepSeek-Prover-V2, DSP+,
  Bourbaki, Goedel-Prover-V2, Ax-Prover (Axiomatic AI), GPT-5 (ReAct, 10
  turns), TIR Conjecturor, Enumerate-Conjecture-Prove.
- **MID** — 2025 agentic/large-compute systems solving 329-500 problems:
  Seed-Prover (ByteDance), AxProverBase (Axiomatic AI), Hilbert, Aleph
  Prover (Logical Intelligence) (avg $23/problem run).
- **STRONG** — systems solving 580-668 problems: Seed-Prover 1.5
  (ByteDance), Goedel-Architect (pass@4), Aleph Prover (Logical
  Intelligence) #2 ($54 avg), Goedel-Architect #2 ($5.8 avg), Aleph Prover
  (Logical Intelligence) #3 ($68 avg). Aleph Prover #3 solved 666/672 and is
  treated as **non-discriminative** — it is still counted in each problem's
  `n_strong`/`strong_solvers`, but excluded from the "discriminative strong
  solver count" used to build the `hard` pool (see step 5). Excluded from
  scoring entirely: Humanfia and Aleph Prover #4 (each claims all 672
  problems solved), and Leanstral 1.5 (claims 588 solved but its `note`
  text lists ids for all 672, making its list unusable). C2C-Goedel,
  C2C-Kimina, and InternLM 7B publish no per-problem list and are also
  excluded.

**3. EASY** = the top 20 problems (within the ≤2024 universe) by a
rarity-weighted weak-solver score:

```
easy_score(p) = Σ_{a ∈ weak solvers of p}  1 / ln(1 + N_a)
```

where `N_a` is the total number of problems approach `a` solved — so a
problem solved by a prover that only solved 7 problems total counts for
more than one solved by a prover that solved 85. Ties are broken by raw
weak-solver count, then by problem id. (`manifest.json`'s `easy_score`
field recomputes this for all 60 problems, for reference, though it is only
meaningful as a ranking within `easy`.)

**4. MEDIUM** = problems solved by **none** of the 19 WEAK approaches and by
**all four** MID approaches (145 such problems in the ≤2024 universe),
further restricted to problems whose Lean file was last modified before
2025-09 (so the statement was stable throughout the MID-tier evaluation
window), then stratified by primary tag (`tags[0]` in the informal-statement
metadata) with fixed quotas: analysis 6, algebra 6, number_theory 3,
linear_algebra 1, geometry 1, combinatorics 1, abstract_algebra 1,
set_theory 1 — picking, within each tag, indices evenly spaced across the
tag's year-sorted candidate list.

**5. HARD** = problems solved by **no WEAK and no MID** approach, and by **at
most 2** of the 4 discriminative STRONG systems (Seed-Prover 1.5,
Goedel-Architect, Aleph Prover #2, Goedel-Architect #2 — Aleph Prover #3
excluded as non-discriminative, see step 2); 54 such problems in the ≤2024
universe. From this pool, 20 were hand-picked:

- All 9 problems solved by **0** discriminative strong systems, except that
  `putnam_2013_a5` (Lean file last modified 2026-08-25) and
  `putnam_2017_b3` (last modified 2026-07-27) were dropped and not
  replaced within the 0-solver group, because their statements were edited
  *after* every evaluation run being scored — meaning their unsolved status
  could be an artifact of a since-fixed formalization bug rather than
  genuine difficulty.
- 11 problems solved by **exactly 1** discriminative strong system, chosen
  by hand to limit the number of Euclidean-geometry problems (whose
  difficulty on this benchmark is often dominated by Mathlib
  formalization/API friction rather than mathematical difficulty) and to
  spread the selection across years and tags.

## Approach tiers (link, solved count, compute budget)

Counts are `lean-wsolution` problems solved out of 672, from
`data/meta.json` / `data/solved.json`.

### WEAK

| Approach                      | Solved | Budget                      | Link                                                                                     |
| ----------------------------- | -----: | --------------------------- | ---------------------------------------------------------------------------------------- |
| GPT-4o                        |      1 | pass@10                     | https://openai.com/index/hello-gpt-4o/                                                   |
| COPRA (GPT-4o)                |      1 | pass@1                      | https://arxiv.org/abs/2310.04353                                                         |
| Deepseek R1                   |      1 | pass@1                      | https://huggingface.co/deepseek-ai/DeepSeek-R1                                           |
| Goedel-Prover-SFT             |      6 | pass@512                    | https://goedel-lm.github.io/                                                             |
| ABEL                          |      7 | pass@596                    | https://openreview.net/forum?id=kk3mSjVCUO                                               |
| InternLM2.5-StepProver        |      6 | pass@2x32x600               | https://arxiv.org/pdf/2410.15700                                                         |
| Self-play Theorem Prover      |      8 | pass@3200                   | https://github.com/kfdong/STP                                                            |
| gemini-2.0-flash-thinking-121 |      1 | pass@1                      | https://deepmind.google/technologies/gemini/flash-thinking/                              |
| gemini-2.5-pro-exp-0325       |      3 | pass@1                      | https://blog.google/technology/google-deepmind/gemini-model-thinking-updates-march-2025/ |
| Kimina-Prover-7B-Distill      |     10 | pass@192                    | https://huggingface.co/AI-MO/Kimina-Prover-Preview-Distill-7B                            |
| o4-mini-high                  |      2 | pass@1                      | https://openai.com/index/introducing-o3-and-o4-mini/                                     |
| DeepSeek-Prover-V2            |     45 | pass@1024                   | https://arxiv.org/abs/2504.21801                                                         |
| DSP+                          |     23 | pass@128                    | https://arxiv.org/abs/2506.11487                                                         |
| Bourbaki                      |     14 | pass@512                    | bourbaki-prover.github.io                                                                |
| Goedel-Prover-V2              |     85 | pass@184                    | https://blog.goedel-prover.com/                                                          |
| Ax-Prover (Axiomatic AI)      |     90 | pass@1, avg. 100 tool calls | https://arxiv.org/pdf/2510.12787                                                         |
| GPT-5 (ReAct, 10 turns)       |     28 | pass@1, 10 tool calls       | https://arxiv.org/abs/2512.00997                                                         |
| TIR Conjecturor               |     14 | pass@4                      | https://github.com/mykhailynab/formal-conjecturer                                        |
| Enumerate-Conjecture-Prove    |     17 | pass@32                     | https://arxiv.org/abs/2505.18492                                                         |

### MID

| Approach                            | Solved | Budget                                | Link                                                  |
| ----------------------------------- | -----: | ------------------------------------- | ----------------------------------------------------- |
| Seed-Prover (ByteDance)             |    329 | MEDIUM                                | https://github.com/ByteDance-Seed/Seed-Prover         |
| AxProverBase (Axiomatic AI)         |    365 | Avg $12.60, Opus 4.5 w/ 50 iterations | https://prover.axiomatic-ai.com                       |
| Hilbert                             |    462 | avg pass@1840                         | https://arxiv.org/pdf/2509.22819                      |
| Aleph Prover (Logical Intelligence) |    500 | Avg $23, Limit $100/problem           | https://www.logicalintelligence.com/aleph-prover.html |

### STRONG

| Approach                               | Solved | Budget                       | Link                                                       | Discriminative?   |
| -------------------------------------- | -----: | ---------------------------- | ---------------------------------------------------------- | ----------------- |
| Seed-Prover 1.5 (ByteDance)            |    581 | 10 H20 days/problem          | https://arxiv.org/abs/2512.17260                           | yes               |
| Goedel-Architect                       |    597 | pass@4, avg $1.47/problem    | https://arxiv.org/abs/2606.06468                           | yes               |
| Aleph Prover (Logical Intelligence) #2 |    635 | Avg $54, Limit $400/problem  | https://www.logicalintelligence.com/aleph-prover_300.html  | yes               |
| Goedel-Architect #2                    |    640 | Avg $5.8/problem             | https://arxiv.org/abs/2606.06468                           | yes               |
| Aleph Prover (Logical Intelligence) #3 |    666 | Avg $68, Limit $1400/problem | https://www.logicalintelligence.com/aleph-prover_1000.html | no (near-ceiling) |

### Excluded from scoring

| Approach                               | Claimed solved | Why excluded                                                                      |
| -------------------------------------- | -------------: | --------------------------------------------------------------------------------- |
| Humanfia                               |            672 | Claims to have solved all problems                                                |
| Aleph Prover (Logical Intelligence) #4 |            672 | Claims to have solved all problems                                                |
| Leanstral 1.5                          |  588 (claimed) | `note` lists ids for all 672 problems, so the per-problem list can't discriminate |
| C2C-Goedel                             |              — | No per-problem list published                                                     |
| C2C-Kimina                             |              — | No per-problem list published                                                     |
| InternLM 7B                            |              — | No per-problem list published                                                     |

## Tier tables

Per problem: the number of WEAK / MID / STRONG approaches (out of 19 / 4 / 5)
that solved it, followed by the names of those approaches, per
`data/scores.json`. Aleph #3 is counted under STRONG but is non-discriminative
(it solved 666/672). Full names, links and budgets are in the approach tables
above; statements and answers are in `manifest.json`.

### easy (sorted by year)

| id               | tags                           | weak                                                                                                                                                                                                                                                                                                                    | mid                                                    | strong                                                                                                        |
| ---------------- | ------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------- |
| `putnam_1971_b1` | abstract_algebra               | **6**: DeepSeek-Prover-V2, DSP+, Bourbaki, Goedel-Prover-V2, Ax-Prover, GPT-5 (ReAct, 10 turns)                                                                                                                                                                                                                         | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1975_a1` | algebra,number_theory          | **5**: DeepSeek-Prover-V2, Goedel-Prover-V2, Ax-Prover, TIR Conjecturor, Enumerate-Conjecture-Prove                                                                                                                                                                                                                     | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1975_b1` | abstract_algebra,number_theory | **6**: DeepSeek-Prover-V2, Goedel-Prover-V2, Ax-Prover, GPT-5 (ReAct, 10 turns), TIR Conjecturor, Enumerate-Conjecture-Prove                                                                                                                                                                                            | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1977_a3` | algebra                        | **16**: Deepseek R1, Goedel-Prover-SFT, ABEL, InternLM2.5-StepProver, Self-play Theorem Prover, gemini-2.0-flash-thinking-121, gemini-2.5-pro-exp-0325, Kimina-Prover-7B-Distill, DeepSeek-Prover-V2, DSP+, Bourbaki, Goedel-Prover-V2, Ax-Prover, GPT-5 (ReAct, 10 turns), TIR Conjecturor, Enumerate-Conjecture-Prove | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1985_a4` | number_theory                  | **6**: DeepSeek-Prover-V2, DSP+, Goedel-Prover-V2, Ax-Prover, GPT-5 (ReAct, 10 turns), Enumerate-Conjecture-Prove                                                                                                                                                                                                       | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1986_a1` | algebra,analysis               | **12**: Goedel-Prover-SFT, ABEL, InternLM2.5-StepProver, Self-play Theorem Prover, Kimina-Prover-7B-Distill, DSP+, Bourbaki, Goedel-Prover-V2, Ax-Prover, GPT-5 (ReAct, 10 turns), TIR Conjecturor, Enumerate-Conjecture-Prove                                                                                          | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1986_a2` | algebra                        | **7**: ABEL, Kimina-Prover-7B-Distill, DeepSeek-Prover-V2, Bourbaki, Goedel-Prover-V2, Ax-Prover, TIR Conjecturor                                                                                                                                                                                                       | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1986_b1` | geometry,algebra               | **13**: Goedel-Prover-SFT, ABEL, InternLM2.5-StepProver, Self-play Theorem Prover, Kimina-Prover-7B-Distill, DeepSeek-Prover-V2, DSP+, Bourbaki, Goedel-Prover-V2, Ax-Prover, GPT-5 (ReAct, 10 turns), TIR Conjecturor, Enumerate-Conjecture-Prove                                                                      | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1988_b1` | number_theory,algebra          | **13**: GPT-4o, COPRA (GPT-4o), Goedel-Prover-SFT, ABEL, InternLM2.5-StepProver, Self-play Theorem Prover, Kimina-Prover-7B-Distill, DeepSeek-Prover-V2, DSP+, Bourbaki, Goedel-Prover-V2, Ax-Prover, GPT-5 (ReAct, 10 turns)                                                                                           | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1988_b2` | algebra                        | **12**: ABEL, InternLM2.5-StepProver, Self-play Theorem Prover, Kimina-Prover-7B-Distill, DeepSeek-Prover-V2, DSP+, Bourbaki, Goedel-Prover-V2, Ax-Prover, GPT-5 (ReAct, 10 turns), TIR Conjecturor, Enumerate-Conjecture-Prove                                                                                         | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1990_a1` | algebra                        | **7**: Self-play Theorem Prover, DeepSeek-Prover-V2, DSP+, Bourbaki, Goedel-Prover-V2, Ax-Prover, Enumerate-Conjecture-Prove                                                                                                                                                                                            | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1991_a2` | linear_algebra                 | **6**: DeepSeek-Prover-V2, Goedel-Prover-V2, Ax-Prover, GPT-5 (ReAct, 10 turns), TIR Conjecturor, Enumerate-Conjecture-Prove                                                                                                                                                                                            | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1993_b1` | algebra                        | **7**: DeepSeek-Prover-V2, DSP+, Bourbaki, Goedel-Prover-V2, Ax-Prover, GPT-5 (ReAct, 10 turns), TIR Conjecturor                                                                                                                                                                                                        | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1995_b4` | algebra                        | **5**: DeepSeek-Prover-V2, Goedel-Prover-V2, Ax-Prover, TIR Conjecturor, Enumerate-Conjecture-Prove                                                                                                                                                                                                                     | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1998_b1` | algebra                        | **6**: DeepSeek-Prover-V2, DSP+, Goedel-Prover-V2, Ax-Prover, TIR Conjecturor, Enumerate-Conjecture-Prove                                                                                                                                                                                                               | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1999_a1` | algebra                        | **5**: DeepSeek-Prover-V2, DSP+, Goedel-Prover-V2, GPT-5 (ReAct, 10 turns), Enumerate-Conjecture-Prove                                                                                                                                                                                                                  | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_2001_a1` | abstract_algebra               | **13**: Goedel-Prover-SFT, ABEL, InternLM2.5-StepProver, Self-play Theorem Prover, gemini-2.5-pro-exp-0325, Kimina-Prover-7B-Distill, o4-mini-high, DeepSeek-Prover-V2, DSP+, Bourbaki, Goedel-Prover-V2, Ax-Prover, GPT-5 (ReAct, 10 turns)                                                                            | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_2005_b1` | algebra                        | **5**: DeepSeek-Prover-V2, DSP+, Goedel-Prover-V2, TIR Conjecturor, Enumerate-Conjecture-Prove                                                                                                                                                                                                                          | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_2008_a1` | algebra                        | **9**: Goedel-Prover-SFT, Self-play Theorem Prover, Kimina-Prover-7B-Distill, DeepSeek-Prover-V2, DSP+, Bourbaki, Goedel-Prover-V2, Ax-Prover, GPT-5 (ReAct, 10 turns)                                                                                                                                                  | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_2012_a2` | abstract_algebra               | **6**: gemini-2.5-pro-exp-0325, o4-mini-high, DeepSeek-Prover-V2, DSP+, Goedel-Prover-V2, GPT-5 (ReAct, 10 turns)                                                                                                                                                                                                       | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |

### medium (sorted by year)

| id               | tags                            | weak     | mid                                                    | strong                                                                                                        |
| ---------------- | ------------------------------- | -------- | ------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------- |
| `putnam_1965_a3` | analysis                        | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1969_b1` | number_theory                   | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1972_a1` | algebra                         | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1972_b2` | analysis                        | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1976_a4` | algebra                         | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1980_b4` | set_theory,combinatorics        | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1982_b5` | analysis                        | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1983_a4` | algebra                         | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1985_b6` | abstract_algebra,linear_algebra | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1994_b1` | algebra                         | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1995_b1` | combinatorics                   | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1996_a5` | number_theory                   | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1996_b2` | analysis                        | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1998_b2` | geometry,algebra                | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_2003_b2` | algebra                         | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_2009_a3` | linear_algebra,analysis         | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_2009_b5` | analysis                        | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_2017_a1` | number_theory                   | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_2017_a2` | algebra                         | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_2018_a5` | analysis                        | **0**: — | **4**: Seed-Prover, AxProverBase, Hilbert, Aleph ($23) | **5**: Seed-Prover 1.5, Goedel-Architect (pass@4), Aleph #2 ($54), Goedel-Architect #2 ($5.8), Aleph #3 ($68) |

### hard (sorted by year)

| id               | tags                         | weak     | mid      | strong                                            |
| ---------------- | ---------------------------- | -------- | -------- | ------------------------------------------------- |
| `putnam_1962_a2` | analysis                     | **0**: — | **0**: — | **2**: Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_1963_a3` | analysis                     | **0**: — | **0**: — | **1**: Aleph #3 ($68)                             |
| `putnam_1967_b1` | geometry                     | **0**: — | **0**: — | **1**: Aleph #3 ($68)                             |
| `putnam_1969_b4` | geometry                     | **0**: — | **0**: — | **1**: Aleph #3 ($68)                             |
| `putnam_1970_b6` | geometry                     | **0**: — | **0**: — | **1**: Aleph #3 ($68)                             |
| `putnam_1974_b1` | algebra,geometry             | **0**: — | **0**: — | **1**: Aleph #3 ($68)                             |
| `putnam_1989_b6` | probability,analysis,algebra | **0**: — | **0**: — | **2**: Aleph #2 ($54), Aleph #3 ($68)             |
| `putnam_1995_a6` | algebra                      | **0**: — | **0**: — | **2**: Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_2000_b3` | analysis                     | **0**: — | **0**: — | **1**: Aleph #3 ($68)                             |
| `putnam_2004_a5` | combinatorics                | **0**: — | **0**: — | **2**: Aleph #2 ($54), Aleph #3 ($68)             |
| `putnam_2014_b6` | analysis,number_theory       | **0**: — | **0**: — | **2**: Aleph #2 ($54), Aleph #3 ($68)             |
| `putnam_2015_b4` | algebra                      | **0**: — | **0**: — | **2**: Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_2017_b6` | algebra,number_theory        | **0**: — | **0**: — | **2**: Aleph #2 ($54), Aleph #3 ($68)             |
| `putnam_2019_a4` | analysis                     | **0**: — | **0**: — | **0**: —                                          |
| `putnam_2021_a6` | number_theory,algebra        | **0**: — | **0**: — | **0**: —                                          |
| `putnam_2022_a5` | combinatorics                | **0**: — | **0**: — | **1**: Aleph #3 ($68)                             |
| `putnam_2022_b6` | analysis                     | **0**: — | **0**: — | **2**: Aleph #2 ($54), Aleph #3 ($68)             |
| `putnam_2023_b5` | number_theory                | **0**: — | **0**: — | **2**: Aleph #2 ($54), Aleph #3 ($68)             |
| `putnam_2024_a3` | combinatorics                | **0**: — | **0**: — | **2**: Goedel-Architect #2 ($5.8), Aleph #3 ($68) |
| `putnam_2024_b5` | combinatorics,algebra        | **0**: — | **0**: — | **2**: Aleph #2 ($54), Aleph #3 ($68)             |

## Caveats

- **Self-reported leaderboard data.** `docs/results.json` and its per-entry
  `note` field are submitted by each approach's authors and parsed with a
  regex over free text (`scripts/parse_lb.py`); solved-problem lists were
  not independently re-verified by re-running any prover. Parsing errors
  (a missed id, a mis-attributed year) are possible, and would silently
  shift counts and, in edge cases, tier assignment.
- **Solved lists refer to older PutnamBench commits.** Every leaderboard
  entry ran against whatever PutnamBench commit existed at submission time,
  not against the commit this subset is pinned to. If a problem's Lean
  statement was corrected between an approach's run and
  `59056d63eebbd01b921945b145182fcf97ec3ac0`, that approach's "solved" or
  "unsolved" status may no longer reflect the current statement. This is
  exactly the risk `finalize.py` tried to control for in the `hard` tier by
  checking `file_last_modified` and dropping the two problems edited after
  every scored evaluation — but the check is coarse (a file-level last-modified
  date, not a diff against the exact statement each approach saw), so
  residual risk remains for problems with several later commits. Several
  `hard`-tier files (e.g. `putnam_1963_a3`, `putnam_1969_b4`) have
  `file_last_modified` dates in 2026 (a batch of statement fixes landed on
  2026-01-06). They were kept because the discriminative STRONG systems that
  matter most for the `hard` criterion ran after those fixes: Goedel-Architect
  (both runs) at commit `9bc55b5` and Aleph Prover #2/#3 at commits
  `8132589`/`961af76`, all later than 2026-01-06. Only Seed-Prover 1.5
  (commit `6df1d4c`, Dec 2025) and the MID systems saw the pre-fix statement,
  so for those files "unsolved by MID" is weaker evidence than for the rest of
  the tier. The two dropped problems (`putnam_2013_a5`, `putnam_2017_b3`)
  were edited in July/August 2026, after every scored evaluation.
- **Geometry is under-represented, deliberately.** The `hard`-tier hand-pick
  explicitly limited Euclidean-geometry problems, because on this benchmark
  geometry difficulty is frequently dominated by Mathlib's geometry API
  surface (coordinate setup, angle/length lemmas) rather than by
  mathematical difficulty proper. This makes `hard` somewhat
  non-representative of PutnamBench geometry as a whole, and should be
  kept in mind when reporting tier-level results.
- **Small-sample tag/year strata.** `medium`'s quotas (analysis 6, algebra
  6, number_theory 3, ..., set_theory 1) and `hard`'s hand-picks are drawn
  from pools of 145 and 54 problems respectively; several tags have quota 1,
  so a single problem stands in for an entire tag and tier-level,
  per-tag comparisons will be noisy.
- **`easy_score` is only a ranking device for the `easy` tier**; it is
  filled in for `medium`/`hard` problems for completeness (all near 0,
  since by construction those tiers have `n_weak = 0`), not because it
  carries selection meaning there.
- **`n_mid`/`n_strong` are constant within `easy` and `medium`.** Every `easy`
  problem has `n_mid = 4` and `n_strong = 5` (all mid/strong approaches
  solved it) and every `medium` problem has `n_mid = 4`, `n_strong = 5`
  as well — expected, since `medium` was defined as exactly "solved by
  all 4 mid approaches", but it means `n_mid`/`n_strong` carry no
  discriminating information within either tier; only `n_weak` does for
  `easy`, and nothing does for `medium` (tag/year stratification is the
  only within-tier structure).
- **`putnam_1997_a1`** appears in PutnamBench's `informal/putnam.json`
  (673 entries) but has no corresponding Lean file (672 files); it is not
  part of any pool here, noted only as a minor inconsistency in the
  upstream data.

## License

- The PutnamBench Lean 4 source files (`lean4/src/*.lean`, and hence the
  `.lean` files in `easy/`, `medium/`, `hard/` here, which are lightly
  rewritten copies of them) are Apache License 2.0, per
  `PutnamBench/lean4/LICENSE`.
- The informal statements and solutions (`informal_statement`,
  `informal_solution` in `manifest.json`/`manifest.csv`) are used with
  permission from the Mathematical Association of America (MAA); see
  `PutnamBench/informal/README.md` and the top-level PutnamBench `README.md`.
  These should not be redistributed outside the terms PutnamBench itself
  operates under.
- This subset's own files (`manifest.json`, `manifest.csv`, this `README.md`,
  and `scripts/parse_lb.py`/`score.py`/`select.py`/`finalize.py`) carry no
  additional license restriction beyond the above; `scripts/rewrite_solutions.py`
  is copied unmodified from PutnamBench and is covered by the same Apache
  2.0 license as the Lean sources it operates on.

## How to run

Every file under `easy/`, `medium/`, and `hard/` is a self-contained Lean 4
file: `import Mathlib` followed by a docstring with the informal statement,
then a `theorem <problem_id> ... := sorry`. To attempt a problem, an agent
just needs a Lean/Mathlib environment matching `v4.27.0` (see "Provenance")
and has to replace the trailing `sorry` with a complete proof; nothing else
in the file should need to change. Problems with a numerical/functional
answer already have that answer substituted into the statement (the
"with-solution" variant — see "Provenance"), so the agent only has to prove
correctness, not also (re)discover the answer.
