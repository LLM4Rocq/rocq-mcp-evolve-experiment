#!/usr/bin/env python3
"""Generate testing/configs/*.json (the 12 Lean arm configs, PORT_SPEC.md
section 4) from their rocq-mcp-evolve source configs.

ONLY system_prompt and task_prompt_template go through textual substitution
(PORT_SPEC.md section 5's table, applied here as an ordered list of literal
`str.replace` pairs -- auditable and exact, per the spec's own requirement).
Every other field (server block, allowed_tools, model, budgets,
mcp_server_name, extra_servers, project_task_copy/prefix_prepend) is
constructed directly from PORT_SPEC.md sections 3/4/6 -- these are NEW Lean
values with no Rocq text to diff against, so they are not part of the
substitution table.

Run standalone:  python3 testing/harness/port_configs.py
Prints, per config: which substitution-table rows fired (and how many
times), then a reverse-substitution self-audit -- applying the SAME table
backwards to the generated Lean prompt must reproduce the Rocq source prompt
BYTE-EXACTLY, which is the mechanical proof that "the only changed spans are
table entries" (PORT_SPEC.md section 5).

(new script; rocq-mcp-evolve authored its configs by hand)
"""

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent            # testing/harness
TESTING = HERE.parent                              # testing/
REPO = TESTING.parent                              # lean-mcp-evolve/
# Source of truth: the `dev` branch of rocq-mcp-evolve-private (commit 4688cd9,
# 2026-09-03, "Merge main (A128 consolidation, A129 logs release) into dev").
# The port was taken from that checkout; re-run this script after pulling `dev`
# and re-check the audit below. At that commit every file this port derives from
# is byte-identical on `main` and `dev` (the branches differ under configs/ and
# harness/ only by main-only team-runner files not used by the held-out matrix).
ROCQ_SOURCE_BRANCH = "dev"
ROCQ_SOURCE_COMMIT = "4688cd9"
ROCQ_CONFIGS = Path("/Users/jviennot/Documents/These/rocq-mcp-evolve-private/configs")
OUT_DIR = TESTING / "configs"
HANDSHAKE_CACHE = HERE / "lean_lsp_mcp_handshake_cache.json"

LEAN_PROJECT = "/Users/jviennot/Documents/Cours/LEAN_2026"

# --------------------------------------------------------------------------
# Section 5 substitution table -- rows that actually fire in one of the 12
# source configs' system_prompt / task_prompt_template (verified by reading
# every source file; see testing/README.md for the full table, including the
# rows below that never fire on these 12 configs and why).
# --------------------------------------------------------------------------
SUBSTITUTIONS = [
    ("expert Rocq (Coq) prover", "expert Lean 4 prover"),
    ("(Rocq 9.1; the file's imports are loaded, and the standard tactic modules "
     "Lia/Lra/Psatz are ALWAYS preloaded — lia, nia, lra, nra, psatz work "
     "everywhere. Never use Require)",
     "(Lean 4 with Mathlib; the file's imports are loaded, and all of Mathlib is "
     "ALWAYS available — simp, omega, norm_num, linarith, nlinarith, positivity, "
     "ring, field_simp work everywhere. Never use import)"),
    ("Target: Rocq 9.1 with its standard library (note: modern Rocq — stdlib is "
     "imported via `From Stdlib Require Import ...`; tactics like lia, nia, lra, "
     "nra, psatz are available when the corresponding modules are imported by "
     "the file).",
     "Target: Lean 4 with Mathlib (note: the file starts with `import Mathlib`; "
     "tactics like simp, omega, norm_num, linarith, nlinarith, positivity, ring, "
     "field_simp are available)."),
    ("(Rocq 9.1)", "(Lean 4 with Mathlib)"),
    (".v file", ".lean file"),
    ("```coq", "```lean"),
    ("The proof must end with Qed.", "The proof must leave no goals open."),
    ("Finish with `Qed.` When a tool reports PROOF COMPLETE, reply with exactly DONE.",
     "When a tool reports PROOF COMPLETE, reply with exactly DONE."),
    ("Never use admit, Admitted, Axiom, Parameter, Hypothesis, Variable, or Require",
     "Never use sorry, admit, axiom, native_decide, set_option, run_tac, #eval, or import"),
    # Case/"extra"-word variant of the row above -- baseline_sonnet.json's
    # actual text is "Never use ... or extra Require" (capital N, WITH
    # "extra"), which matches neither PORT_SPEC.md's row10 (no "extra") nor
    # row11 (lowercase "never") verbatim. Same substance as both; added so
    # the reverse-substitution audit below is exact. See README deviations.
    ("Never use admit, Admitted, Axiom, Parameter, Hypothesis, Variable, or extra Require",
     "Never use sorry, admit, axiom, native_decide, set_option, run_tac, #eval, or extra import"),
    ("never use admit, Admitted, Axiom, Parameter, Hypothesis, Variable, or extra Require",
     "never use sorry, admit, axiom, native_decide, set_option, run_tac, #eval, or extra import"),
    ("No admit, Admitted, Axiom, Parameter, Hypothesis, Variable, or extra Require",
     "No sorry, admit, axiom, native_decide, set_option, run_tac, #eval, or extra import"),
    ("(lia, lra, nra, nia, field_simp variants, ring, psatz...)",
     "(simp, omega, norm_num, linarith, nlinarith, positivity, ring, field_simp variants, aesop...)"),
    ('["nra.", "nia.", "field_simp. nra.", "assert (H := sq_nonneg (a-b)). nra."]',
     '["nlinarith", "positivity", "field_simp; ring", "nlinarith [sq_nonneg (a-b)]"]'),
    ("execute sentences directly", "execute tactics directly, one per line"),
    ("Also for queries: `Search (_ <= _)%R.` `Check Rmult_le_compat.`",
     "Also for queries: `#check mul_le_mul` `exact?`"),
    ("undo the last count committed sentences", "undo the last count committed tactics"),
]

# row19 (sibling toolset sentence) needs the REAL lean-lsp-mcp tool names,
# filled in below from the captured handshake cache if present.
ROCQ_MCP_TOOLSET_SENTENCE = (
    "You have the rocq-mcp toolset: interactive proving (rocq_start to open a "
    "session on the statement, rocq_check to run tactics with cached imports, "
    "rocq_step_multi to test several tactics at once), compilation (rocq_compile "
    "for full source), search (rocq_query), and verification (rocq_verify)."
)


def load_leanlsp_tools():
    if not HANDSHAKE_CACHE.exists():
        return None
    cache = json.loads(HANDSHAKE_CACHE.read_text())
    return [t["name"] for t in cache["tools"]["tools"]]


def build_sibling_substitution():
    tools = load_leanlsp_tools()
    if tools is None:
        lean_sentence = (
            "You have the lean-lsp-mcp toolset: TODO -- handshake capture "
            "unavailable when this config was generated; re-run "
            "testing/harness/capture_handshake.py then "
            "testing/harness/port_configs.py to fill in the real tool names."
        )
        return [(ROCQ_MCP_TOOLSET_SENTENCE, lean_sentence)], None
    # 1:1 conceptual mapping to the Rocq toolset sentence's four clauses:
    #   interactive proving   -> lean_goal, lean_diagnostic_messages, lean_multi_attempt
    #   compilation            -> lean_run_code (full source, like rocq_compile)
    #   search                 -> lean_loogle / lean_leansearch / lean_state_search
    #   verification            -> lean_verify (name literally carries over)
    lean_sentence = (
        "You have the lean-lsp-mcp toolset: interactive proving (lean_goal to see "
        "proof goals at a position in the task file, lean_diagnostic_messages to "
        "check compiler diagnostics, lean_multi_attempt to test several tactics at "
        "once), compilation (lean_run_code for full source), search (lean_loogle, "
        "lean_leansearch, lean_state_search), and verification (lean_verify)."
    )
    return [(ROCQ_MCP_TOOLSET_SENTENCE, lean_sentence)], tools


SIBLING_SUBS, LEANLSP_TOOLS = build_sibling_substitution()


def apply_subs(text, subs):
    """Apply substitutions in order; return (new_text, [(old,new,count), ...])."""
    report = []
    for old, new in subs:
        n = text.count(old)
        if n:
            text = text.replace(old, new)
        report.append((old, new, n))
    return text, report


def reverse_audit(rocq_text, lean_text, subs):
    """Apply subs BACKWARDS (new->old, reverse order) to lean_text; must
    reproduce rocq_text exactly. Returns None if OK, else a diff string."""
    reconstructed = lean_text
    for old, new in reversed(subs):
        reconstructed = reconstructed.replace(new, old)
    if reconstructed == rocq_text:
        return None
    return (f"MISMATCH: reverse-substitution did not reproduce the Rocq source.\n"
            f"  rocq_text        = {rocq_text!r}\n"
            f"  lean_text        = {lean_text!r}\n"
            f"  reconstructed    = {reconstructed!r}")


# --------------------------------------------------------------------------
# Section 4 arm table -> per-config server blocks
# --------------------------------------------------------------------------

def evolve_server():
    return {
        "server": {
            # prewarm proxy in front of our own server (README deviation 16)
            "command": "/usr/bin/python3",
            "args": ["-S", "{repo}/testing/harness/mcp_prewarm_proxy.py",
                     "--cache", "{repo}/testing/harness/handshake_cache_evolve5.json",
                     "{repo}/.lake/build/bin/lean-mcp-evolve"],
            "env": {
                "LEAN_ENABLE_TOOLS": "step,rollback,state,try,auto_close",
                "LEAN_HINTS": "1",
                "LEAN_SUGGEST": "1",
                "LEAN_ENV_V2": "1",
                "LEAN_AUTO2": "0",
                "LEAN_AUTO_SEARCH": "0",
                "LEAN_PRELOAD": "0",
                "LEAN_IMPORT_ECHO": "0",
                "LEAN_STEP_TIMEOUT": "30",
                "LEAN_TRY_TIMEOUT": "15",
                "LEAN_AUTO_TIMEOUT": "6",
                "LEAN_OPEN_TIMEOUT": "600",
                "LEAN_MAX_HEARTBEATS": "200000",
            },
        },
        "mcp_server_name": "lean",
        "allowed_tools": [
            "mcp__lean__step", "mcp__lean__rollback", "mcp__lean__state",
            "mcp__lean__try", "mcp__lean__auto_close",
        ],
    }


def baseline_server():
    return {
        "server": {
            "command": "/usr/bin/python3",
            "args": ["-S", "{repo}/testing/harness/mcp_prewarm_proxy.py",
                     "--cache", "{repo}/testing/harness/handshake_cache_baseline.json",
                     "{repo}/.lake/build/bin/lean-mcp-baseline"],
            "env": {"LEAN_COMPILE_TIMEOUT": "60"},
        },
        "mcp_server_name": "lean",
        "allowed_tools": ["mcp__lean__check"],
    }


def sibling_server():
    tools = LEANLSP_TOOLS or ["TODO_lean_lsp_mcp_tool"]
    return {
        "server": {
            "command": "/usr/bin/python3",
            "args": ["-S", "{repo}/testing/harness/mcp_prewarm_proxy.py",
                     "uvx", "lean-lsp-mcp"],
            "env": {"LEAN_PROJECT_PATH": LEAN_PROJECT},
        },
        "mcp_server_name": "leanlsp",
        "extra_servers": {
            "final": {"command": "/usr/bin/python3",
                      "args": ["-S", "{repo}/testing/harness/mcp_prewarm_proxy.py",
                               "--cache", "{repo}/testing/harness/handshake_cache_submit.json",
                               "{repo}/.lake/build/bin/lean-mcp-submit"]},
        },
        "allowed_tools": [f"mcp__leanlsp__{t}" for t in tools] + ["mcp__final__submit"],
        # Bridge (section 6): lean-lsp-mcp is LSP-backed and needs the task
        # file to actually exist inside its configured project to diagnose
        # it; run_eval.py copies task.lean there before launch and deletes
        # it after. {aid}/{task_rel} substituted by run_eval.py.
        "project_task_copy": "PutnamEval/{aid}.lean",
        "prefix_prepend": "-- task file: {task_rel}\n",
    }


ARMS = [
    # lean_config_id, rocq_config_id, model, max_turns, wall_s, server_fn, extra_subs
    ("frozen", "frozen", "claude-haiku-4-5", 30, 300, evolve_server, []),
    ("frozen_wallonly", "frozen_wallonly", "claude-haiku-4-5", 200, 300, evolve_server, []),
    ("baseline_sonnet", "baseline_sonnet", "claude-sonnet-5", 30, 300, baseline_server, []),
    ("session_try_hints_auto_sonnet", "session_try_hints_auto_sonnet", "claude-sonnet-5", 30, 300, evolve_server, []),
    ("lean_lsp_mcp_fair_sonnet", "rocq_mcp_fair_sonnet", "claude-sonnet-5", 30, 300, sibling_server, SIBLING_SUBS),
    ("af_pf_baseline", "af_pf_baseline", "claude-sonnet-5", 100, 300, baseline_server, []),
    ("af_pf_session", "af_pf_session", "claude-sonnet-5", 100, 300, evolve_server, []),
    ("af_pf_session2", "af_pf_session2", "claude-sonnet-5", 100, 300, evolve_server, []),
    ("af_pf_lean_lsp_mcp", "af_pf_rocqmcp", "claude-sonnet-5", 100, 300, sibling_server, []),
    ("af_pf_baseline_opus", "af_pf_baseline_opus", "claude-opus-4-8", 100, 300, baseline_server, []),
    ("af_pf_session2_opus", "af_pf_session2_opus", "claude-opus-4-8", 100, 300, evolve_server, []),
    ("af_pf_lean_lsp_mcp_opus", "af_pf_rocqmcp_opus", "claude-opus-4-8", 100, 300, sibling_server, []),
]


def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    any_mismatch = False
    for lean_id, rocq_id, model, max_turns, wall_s, server_fn, extra_subs in ARMS:
        rocq_cfg = json.loads((ROCQ_CONFIGS / f"{rocq_id}.json").read_text())
        subs = SUBSTITUTIONS + extra_subs
        sys_lean, sys_report = apply_subs(rocq_cfg["system_prompt"], subs)
        task_lean, task_report = apply_subs(rocq_cfg["task_prompt_template"], subs)

        mismatch = reverse_audit(rocq_cfg["system_prompt"], sys_lean, subs)
        mismatch2 = reverse_audit(rocq_cfg["task_prompt_template"], task_lean, subs)

        block = server_fn()
        lean_cfg = {
            "config_id": lean_id,
            "description": (f"Ported from rocq-mcp-evolve config '{rocq_id}' "
                             f"(PORT_SPEC.md sections 4-5). {rocq_cfg.get('description', '')}"),
            **block,
            "model": model,
            "max_turns": max_turns,
            "attempt_timeout_s": wall_s,
            "system_prompt": sys_lean,
            "task_prompt_template": task_lean,
        }
        out_path = OUT_DIR / f"{lean_id}.json"
        out_path.write_text(json.dumps(lean_cfg, indent=1, ensure_ascii=False) + "\n")

        fired = [f"  [{n}x] {old[:60]!r} -> {new[:60]!r}"
                 for old, new, n in sys_report + task_report if n]
        print(f"== {lean_id}  (from {rocq_id}) ==")
        for line in fired:
            print(line)
        if mismatch:
            any_mismatch = True
            print(f"  !! system_prompt audit: {mismatch}")
        if mismatch2:
            any_mismatch = True
            print(f"  !! task_prompt_template audit: {mismatch2}")
        if not mismatch and not mismatch2:
            print("  audit: OK (reverse-substitution reproduces the Rocq source exactly)")
        print(f"  wrote {out_path}")

    # Derived configs (not in the Rocq matrix): (lean_id, base_lean_id, overrides, note)
    # Prompts for the tool-complete workspace arm (user request 2026-09-07):
    # written in the shape of the Rocq autoformalization prompts (af_tools2
    # system prompt: role + workspace workflow + "you additionally have a
    # live prover" paragraph + verify-before-DONE; af3 task prompt: "grading
    # is machine-checked on your delivered files only" clause), with the
    # phase-1 proving prompt's tool guidance (auto_close first, try as the
    # main tool, DONE/GIVEUP) and the Lean forbidden-token list.
    AF_TOOLS_SYSTEM_PROMPT = (
        "You are an expert Lean 4 prover (Lean 4 with Mathlib; all of Mathlib is available — simp, omega, "
        "norm_num, linarith, nlinarith, positivity, ring, field_simp work everywhere). You must PROVE a "
        "Putnam theorem that is given as a file in your workspace: a Lake project already built against "
        "Mathlib, on which all your tools operate (paths are relative to its root).\n\n"
        "Workspace tools (files): write_file{path, content} creates or overwrites a file (parent "
        "directories are created); read_file{path} reads one; list_dir{} lists the tree; lake_build{} runs "
        "`lake build` at the workspace root and returns ALL errors across all files; verify{} checks the "
        "workspace against the grader's rules (a forbidden-token scan of every .lean file plus a clean "
        "lake build) — call it before replying DONE and fix everything it reports.\n\n"
        "Prover tools (lean): a LIVE prover session; the target theorem is already open at launch and its "
        "goal is shown by state{}. open{file, theorem?} starts (or restarts) a session on a workspace file "
        "(default: the first theorem that errors or uses sorry); build{file} diagnoses a whole file, "
        "reporting EVERY broken proof in one call; check{script} submits a complete tactic script with "
        "repair-from-failure (the valid prefix stays committed and you stand at the failing tactic); "
        "step{text} executes tactics one per line (each success commits permanently; on failure you get "
        "the error and the state after the last success; also for queries: `#check mul_le_mul` `exact?`); "
        "try{candidates:[...]} tests up to 8 alternative tactic scripts against the current goal IN ONE "
        "CALL and commits the first that fully succeeds, showing what every other candidate would do — "
        "this is your main tool: propose several plausible attacks at once (e.g. [\"nlinarith\", "
        "\"positivity\", \"field_simp; ring\", \"nlinarith [sq_nonneg (a-b)]\"]); auto_close{} runs the "
        "whole standard finisher portfolio (simp, omega, norm_num, linarith, nlinarith, positivity, ring, "
        "field_simp variants, aesop...) against the current goal in ONE call and commits a success — call "
        "it FIRST on every new goal, and again after each structural step; rollback{count} undoes the last "
        "count committed tactics; state{} shows the goals and the proof so far; verify{} (lean) is a clean "
        "lake build of the project plus the forbidden-token scan.\n\n"
        "Recommended workflow: attack the open goal with auto_close, then try with several candidate "
        "scripts at once, refining with step; when the session reports PROOF COMPLETE, write the returned "
        "finished declaration into the theorem's file with write_file (in place of its `sorry`), then "
        "lake_build and verify. Scratch files for experiments are welcome (e.g. Putnam/Scratch.lean), but "
        "the delivered proof must be self-contained inside the target theorem: its imports, its statement "
        "and everything outside its proof must stay EXACTLY as given.\n\n"
        "Strict rules:\n"
        "- Never use sorry, admit, axiom, native_decide, set_option, run_tac, #eval, or unsafe in the "
        "delivered file — an external checker rejects them.\n"
        "- Reply with exactly DONE when the proof is written to the file and verify passes. If you "
        "conclude you cannot finish, reply with exactly GIVEUP.")
    AF_TOOLS_TASK_PROMPT = (
        "Prove the theorem below. It is the file `{task_file}` of the Lake project in your workspace "
        "(already built against Mathlib); the theorem is already open in the prover session and its goal "
        "is shown by state{{}}.\n\n"
        "Grading is machine-checked on your delivered file only: (1) `{task_file}` must compile with your "
        "proof written in place of `sorry`; (2) everything outside the theorem's proof — imports, "
        "definitions, the statement — must stay EXACTLY as provided, character for character; (3) the "
        "proof must be free of sorry, admit, axiom, native_decide, set_option, run_tac, #eval and unsafe, "
        "and must not introduce axioms. Other files you create in the workspace are not graded (use them "
        "as scratch space).\n\n"
        "```lean\n{prefix}```\n\n"
        "Use the tools; call verify{{}} before replying DONE. When the proof is complete and verified, "
        "reply DONE.")

    DERIVED = [
        ("session_try_hints_auto_sonnet_wallonly", "session_try_hints_auto_sonnet",
         {"max_turns": 200},
         "wall-only variant (2026-09-06, user decision): identical except the 30-turn cap "
         "is lifted to the 200 safety rail (A63/A100 wall-only convention, as "
         "frozen_wallonly is to frozen); the turn cap was measured to be a covert "
         "tool-call tax (A62b)."),
        # AF_TOOLS_SPEC.md sections 2-4 (2026-09-07, user decision): rerun the
        # medium5 test with the SAME model/budgets/prompts as
        # session_try_hints_auto_sonnet_wallonly (kept byte-identical, see
        # the audit in testing/README.md) but with the tool surface of the
        # Rocq autoformalization arm `af3_evolve` -- the files sidecar
        # (write_file/read_file/list_dir/lake_build/verify) + all NINE
        # prover tools (LEAN_ENABLE_TOOLS unset, evolve_server()'s default)
        # -- and a per-problem Lake project workspace the model can create
        # and manage files in ("workspace": "lake_putnam", run_eval.py
        # section 2).
        ("session_af_tools_sonnet_wallonly", "session_try_hints_auto_sonnet_wallonly",
         {
             "server": {
                 "command": "/usr/bin/python3",
                 "args": ["-S", "{repo}/testing/harness/mcp_prewarm_proxy.py",
                          "--cache", "{repo}/testing/harness/handshake_cache_evolve9.json",
                          "{repo}/.lake/build/bin/lean-mcp-evolve"],
                 # same as evolve_server()'s env WITHOUT LEAN_ENABLE_TOOLS
                 # (unset -> the server's default of all nine tools).
                 "env": {
                     "LEAN_HINTS": "1",
                     "LEAN_SUGGEST": "1",
                     "LEAN_ENV_V2": "1",
                     "LEAN_AUTO2": "0",
                     "LEAN_AUTO_SEARCH": "0",
                     "LEAN_PRELOAD": "0",
                     "LEAN_IMPORT_ECHO": "0",
                     "LEAN_STEP_TIMEOUT": "30",
                     "LEAN_TRY_TIMEOUT": "15",
                     "LEAN_AUTO_TIMEOUT": "6",
                     "LEAN_OPEN_TIMEOUT": "600",
                     "LEAN_MAX_HEARTBEATS": "200000",
                 },
             },
             "mcp_server_name": "lean",
             "extra_servers": {
                 "files": {
                     "command": "/usr/bin/python3",
                     "args": ["-S", "{repo}/testing/harness/mcp_prewarm_proxy.py",
                              "--cache", "{repo}/testing/harness/handshake_cache_files.json",
                              "{repo}/.lake/build/bin/lean-mcp-files"],
                     "env": {},
                 },
             },
             "allowed_tools": [
                 "mcp__files__write_file", "mcp__files__read_file", "mcp__files__list_dir",
                 "mcp__files__lake_build", "mcp__files__verify",
                 "mcp__lean__open", "mcp__lean__build", "mcp__lean__check", "mcp__lean__step",
                 "mcp__lean__try", "mcp__lean__auto_close", "mcp__lean__state",
                 "mcp__lean__rollback", "mcp__lean__verify",
             ],
             "workspace": "lake_putnam",
         },
         "AF_TOOLS_SPEC.md (2026-09-07, user decision): the tool surface of the Rocq "
         "autoformalization arm 'af3_evolve' (rocq-mcp-evolve-private configs/af3_evolve.json) "
         "ported rocq->lean, dune_build->lake_build -- the files sidecar (write_file, "
         "read_file, list_dir, lake_build, verify) plus all nine prover tools (open, build, "
         "check, step, try, auto_close, state, rollback, verify; LEAN_ENABLE_TOOLS unset) "
         "against a per-problem Lake project workspace (\"workspace\": \"lake_putnam\") the "
         "model can create and manage files in. model/max_turns/attempt_timeout_s/"
         "system_prompt/task_prompt_template are kept BYTE-IDENTICAL to "
         "session_try_hints_auto_sonnet_wallonly (user instruction: keep the other "
         "configuration). Caveat: the system prompt still describes only the five frozen "
         "tools (kept verbatim); the other nine tools are documented to the model only by "
         "their own shipped MCP tool descriptions -- the Rocq af3 arms were prompt-free with "
         "the server README injected instead, an alternative protocol not used here."),
        ("session_af_tools_prompted_sonnet_wallonly", "session_af_tools_sonnet_wallonly",
         {"system_prompt": AF_TOOLS_SYSTEM_PROMPT, "task_prompt_template": AF_TOOLS_TASK_PROMPT},
         "prompted variant (2026-09-07, user request): same tool surface, workspace, budget and env as "
         "session_af_tools_sonnet_wallonly, but the system and task prompts describe ALL fourteen tools "
         "and the workspace, in the shape of the Rocq autoformalization prompts (af_tools2 system prompt, "
         "af3 task-prompt grading clause). {task_file} = the theorem's workspace-relative path."),
    ]

    for lean_id, base_id, overrides, note in DERIVED:
        base = json.loads((OUT_DIR / f"{base_id}.json").read_text())
        base["config_id"] = lean_id
        base["description"] = base["description"] + " | " + note
        base.update(overrides)
        (OUT_DIR / f"{lean_id}.json").write_text(json.dumps(base, indent=1, ensure_ascii=False) + "\n")
        print(f"== {lean_id}  (derived from {base_id}: {overrides}) ==\n  wrote {OUT_DIR / (lean_id + '.json')}")

    # -----------------------------------------------------------------
    # Two more arms of the workspace setting (TWO_ARMS_SPEC.md, user
    # request 2026-09-08): both derive from session_af_tools_prompted_sonnet_wallonly
    # (kept as the base -- same workspace/budget/env), each swapping the
    # tool surface for one Rocq autoformalization sibling: af3_base (files
    # sidecar ONLY, no live prover -- af_compiler_only_*) and af3_sota
    # (files sidecar + the lean-lsp-mcp SOTA sibling, in place of the Rocq
    # tools -- af_lean_lsp_mcp_*). Unlike the Rocq af3 arms, both stay
    # PROMPTED (system_prompt != ""), following the af_tools2/af3 prompt
    # shape used for session_af_tools_prompted_sonnet_wallonly, not the
    # Rocq arms' prompt-free + {readme}-injection protocol (see the
    # README's "Arms: compiler-only control and lean-lsp-mcp sibling in
    # the workspace setting" subsection for the choice).
    AF_BASE = json.loads((OUT_DIR / "session_af_tools_prompted_sonnet_wallonly.json").read_text())
    AF_ROLE_PARA = (
        "You are an expert Lean 4 prover (Lean 4 with Mathlib; all of Mathlib is available — simp, omega, "
        "norm_num, linarith, nlinarith, positivity, ring, field_simp work everywhere). You must PROVE a "
        "Putnam theorem that is given as a file in your workspace: a Lake project already built against "
        "Mathlib, on which all your tools operate (paths are relative to its root).")
    AF_FILES_PARA = (
        "Workspace tools (files): write_file{path, content} creates or overwrites a file (parent "
        "directories are created); read_file{path} reads one; list_dir{} lists the tree; lake_build{} runs "
        "`lake build` at the workspace root and returns ALL errors across all files; verify{} checks the "
        "workspace against the grader's rules (a forbidden-token scan of every .lean file plus a clean "
        "lake build) — call it before replying DONE and fix everything it reports.")
    AF_STRICT_RULES = (
        "Strict rules:\n"
        "- Never use sorry, admit, axiom, native_decide, set_option, run_tac, #eval, or unsafe in the "
        "delivered file — an external checker rejects them.\n"
        "- Reply with exactly DONE when the proof is written to the file and verify passes. If you "
        "conclude you cannot finish, reply with exactly GIVEUP.")
    AF_SCRATCH_SENTENCE = (
        " Scratch files for experiments are welcome (e.g. Putnam/Scratch.lean), but the delivered proof "
        "must be self-contained inside the target theorem: its imports, its statement and everything "
        "outside its proof must stay EXACTLY as given.")

    # Arm 1 (mirrors Rocq af3_base): files sidecar ONLY -- no live prover,
    # no MCP server named "lean" at all.
    AF_COMPILER_SYSTEM_PROMPT = "\n\n".join([
        AF_ROLE_PARA,
        AF_FILES_PARA,
        ("Recommended workflow: read the file, write your proof in place of `sorry` with write_file, "
         "lake_build, read the errors, fix, repeat; call verify before replying DONE." + AF_SCRATCH_SENTENCE),
        AF_STRICT_RULES,
    ])

    # Arm 2 (mirrors Rocq af3_sota): files sidecar + the lean-lsp-mcp SOTA
    # sibling (in place of the Rocq af3_sota's rocq-mcp). Tool coverage
    # written from lean_lsp_mcp_readme_excerpt.md (README + docs/tools.md)
    # and the captured handshake's own tool descriptions.
    # Validated 2026-09-08 against a real per-problem workspace (see
    # leanlsp_validation.md in the port's scratchpad, folded in here):
    # lean-lsp-mcp never edits files itself; file_path is workspace-root-
    # relative; line/column are 1-indexed (columns count codepoints); an
    # edit made via write_file is picked up by the NEXT lean_* call with no
    # reload needed; no prior `lake build` of the target file is required
    # for diagnostics. CRITICAL: the dataset ships the hole as a TERM-mode
    # `:= sorry` (no `by`) -- at that position lean_goal returns
    # `no_goal_at_position` and lean_multi_attempt snippets fail with
    # "Unknown identifier" (tactic names parse as bare terms there). The
    # model must first rewrite the hole to a `by` block via write_file
    # before lean_goal/lean_multi_attempt expose a real tactic goal.
    AF_LEANLSP_PARA = (
        "Prover tools (leanlsp): You additionally have the lean-lsp-mcp toolset, a live Lean Language "
        "Server bound to your workspace. It does NOT edit files itself — use write_file for that; every "
        "file_path argument is relative to the workspace root, line and column are 1-indexed (columns "
        "count codepoints), and after you edit a file with write_file the LSP re-checks it automatically "
        "on the next call, no reload needed. lean_goal{file_path, line, column?} and "
        "lean_term_goal{file_path, line, column?} show the tactic/term goal at a position (omit column for "
        "goals_before/goals_after) — ONLY inside a `by` tactic block: the theorem's hole starts as a "
        "TERM-mode `:= sorry`, which has no tactic goal to query (lean_goal returns "
        "'no_goal_at_position' there and lean_multi_attempt's tactic snippets fail with 'Unknown "
        "identifier'), so first rewrite it with write_file to `:= by` followed by an indented `sorry` line "
        "before using lean_goal or lean_multi_attempt; lean_diagnostic_messages{file_path} lists every "
        "compiler error/warning in a file and works on the raw term-mode file too (no `by` needed, no "
        "prior lake_build needed either); lean_hover_info{file_path, line, column} shows a symbol's type "
        "and docs; lean_completions{file_path, line, column} lists identifiers valid at a position; "
        "lean_multi_attempt{file_path, line, snippets} tests several tactic snippets against the goal at a "
        "line WITHOUT modifying the file (same `by`-block requirement as lean_goal) — screen candidates "
        "here before writing one; lean_run_code{code} compiles a self-contained snippet (with its own "
        "imports); lean_leansearch, lean_loogle, lean_local_search, lean_state_search and "
        "lean_hammer_premise search for lemmas (natural language, type pattern, local declarations, "
        "goal-directed, and premise-suggestion respectively); lean_verify{file_path, theorem_name} audits "
        "a theorem's axioms plus a forbidden-pattern source scan; lean_build{} runs `lake build` and "
        "restarts the LSP — SLOW, only needed after new imports, diagnostics work without it; "
        "lean_file_outline{file_path} lists a file's declarations; lean_declaration_file{file_path, "
        "symbol} shows where a symbol is defined.")
    AF_LSP_SYSTEM_PROMPT = "\n\n".join([
        AF_ROLE_PARA,
        AF_FILES_PARA,
        AF_LEANLSP_PARA,
        ("Recommended workflow: first rewrite the theorem's `:= sorry` to `:= by` with an indented `sorry` "
         "line via write_file, so lean_goal/lean_multi_attempt see a real tactic state; then use lean_goal "
         "and lean_diagnostic_messages to see the current goal and errors, lean_multi_attempt to screen "
         "candidate tactics before committing one with write_file, and the search tools (lean_leansearch, "
         "lean_loogle, lean_local_search, lean_state_search, lean_hammer_premise) to find lemmas; then "
         "lake_build and verify (files) before replying DONE." + AF_SCRATCH_SENTENCE),
        AF_STRICT_RULES,
    ])

    # Shared task prompt for both new arms: AF_TOOLS_TASK_PROMPT with the
    # session clause removed (no live prover session in either arm).
    AF_NOSESSION_TASK_PROMPT = AF_TOOLS_TASK_PROMPT.replace(
        "; the theorem is already open in the prover session and its goal is shown by state{{}}", "")
    assert AF_NOSESSION_TASK_PROMPT != AF_TOOLS_TASK_PROMPT, "session clause not found to remove"

    FILES_SERVER_BLOCK = {
        "command": "/usr/bin/python3",
        "args": ["-S", "{repo}/testing/harness/mcp_prewarm_proxy.py",
                 "--cache", "{repo}/testing/harness/handshake_cache_files.json",
                 "{repo}/.lake/build/bin/lean-mcp-files"],
        "env": {},
    }
    FILES_ALLOWED_TOOLS = [
        "mcp__files__write_file", "mcp__files__read_file", "mcp__files__list_dir",
        "mcp__files__lake_build", "mcp__files__verify",
    ]
    # `uvx lean-lsp-mcp --version` at the time this was written: 0.30.0,
    # matching the captured handshake's serverInfo.version -- pinned here
    # (TWO_ARMS_SPEC.md: "if uvx can pin, use the pinned spec in args").
    LEAN_LSP_MCP_VERSION = "0.30.0"

    TWO_ARMS = [
        ("af_compiler_only_prompted_sonnet_wallonly",
         {
             "description": AF_BASE["description"] + " | TWO_ARMS_SPEC.md (2026-09-08, user request): "
                 "mirrors the Rocq autoformalization arm 'af3_base' -- the files sidecar ONLY (write_file, "
                 "read_file, list_dir, lake_build, verify), no live prover / no 'lean' MCP server at all. "
                 "Same workspace/budget/env as session_af_tools_prompted_sonnet_wallonly. Prompted (not "
                 "prompt-free like af3_base): system_prompt keeps the role sentence, the workspace-tools "
                 "paragraph, the scratch-files sentence and the strict rules byte-identical to the base "
                 "arm's, with the Prover-tools paragraph removed and the workflow paragraph rewritten for "
                 "the compiler-only edit/build/fix loop.",
             "server": FILES_SERVER_BLOCK,
             "mcp_server_name": "files",
             "extra_servers": {},
             "allowed_tools": FILES_ALLOWED_TOOLS,
             "system_prompt": AF_COMPILER_SYSTEM_PROMPT,
             "task_prompt_template": AF_NOSESSION_TASK_PROMPT,
         }),
        ("af_lean_lsp_mcp_prompted_sonnet_wallonly",
         {
             "description": AF_BASE["description"] + " | TWO_ARMS_SPEC.md (2026-09-08, user request): "
                 "mirrors the Rocq autoformalization arm 'af3_sota' -- the files sidecar PLUS the "
                 f"lean-lsp-mcp SOTA sibling (v{LEAN_LSP_MCP_VERSION}, pinned) in place of rocq-mcp, "
                 "LEAN_PROJECT_PATH pointed at the attempt's own workspace ('{workspace}', substituted by "
                 "run_eval.py). No submit sidecar, no project_task_copy/prefix_prepend -- the workspace IS "
                 "the Lean project, so lean-lsp-mcp opens the task file directly and delivery is the "
                 "workspace file (graded the same way as every other lake_putnam-workspace arm). Prompted "
                 "(not prompt-free + {readme}-injected like af3_sota): the Prover-tools paragraph names the "
                 "real lean-lsp-mcp tools (written from lean_lsp_mcp_readme_excerpt.md) and the workflow "
                 "paragraph is rewritten for the LSP-diagnose/search/edit loop; everything else "
                 "byte-identical to the base arm's system prompt.",
             "server": {
                 "command": "/usr/bin/python3",
                 "args": ["-S", "{repo}/testing/harness/mcp_prewarm_proxy.py",
                          "uvx", f"lean-lsp-mcp@{LEAN_LSP_MCP_VERSION}"],
                 "env": {"LEAN_PROJECT_PATH": "{workspace}"},
             },
             "mcp_server_name": "leanlsp",
             # extra_servers.files inherited unchanged from the base arm (identical block).
             "allowed_tools": [f"mcp__leanlsp__{t}" for t in (LEANLSP_TOOLS or ["TODO_lean_lsp_mcp_tool"])]
                 + FILES_ALLOWED_TOOLS,
             "system_prompt": AF_LSP_SYSTEM_PROMPT,
             "task_prompt_template": AF_NOSESSION_TASK_PROMPT,
         }),
    ]
    for lean_id, overrides in TWO_ARMS:
        cfg = dict(AF_BASE)
        cfg["config_id"] = lean_id
        cfg.update(overrides)
        (OUT_DIR / f"{lean_id}.json").write_text(json.dumps(cfg, indent=1, ensure_ascii=False) + "\n")
        print(f"== {lean_id}  (derived from session_af_tools_prompted_sonnet_wallonly) ==\n"
              f"  wrote {OUT_DIR / (lean_id + '.json')}")

    # -----------------------------------------------------------------
    # Prompt-free workspace arms (PF_WS_SPEC.md, user request 2026-09-09):
    # the same three-way comparison as the two workspace arms above
    # (compiler-only / evolve-nine-tools / lean-lsp-mcp) but PROMPT-FREE
    # (system_prompt "" -- the A80 rules live in the task prompt exactly as
    # already ported by the ARMS loop above) and WITHOUT the files sidecar
    # in any arm. Each derives from its af_pf_* port (af_pf_baseline /
    # af_pf_session2 / af_pf_rocqmcp's Lean port af_pf_lean_lsp_mcp) so
    # system_prompt/task_prompt_template stay byte-identical to the base
    # arm's -- already proven byte-exact against the Rocq source by the
    # reverse-substitution audit run above when that base arm itself was
    # generated; only server/allowed_tools/mcp_server_name/extra_servers/
    # workspace/max_turns are overridden here, exactly as for the
    # TWO_ARMS derivation above.
    PF_WS = [
        ("af_pf_ws_baseline_sonnet_wallonly", "af_pf_baseline",
         {"max_turns": 200, "workspace": "lake_putnam"},
         "PF_WS_SPEC.md (2026-09-09, user request): Rocq naive control (ONE tool, "
         "lean-mcp-baseline behind the prewarm proxy) rerun in the per-problem Lake "
         "workspace setting -- server/allowed_tools/mcp_server_name/system_prompt/"
         "task_prompt_template kept BYTE-IDENTICAL to af_pf_baseline (LEAN_PROJECT_ROOT "
         "is set to the workspace automatically by run_eval.py's workspace branch, so "
         "`lake env lean` resolves the shared Mathlib there); only max_turns (100 -> "
         "200, the wall-only rail) and workspace are overridden. Delivery: the server "
         "writes candidate.lean on exit 0 (existing contract), unchanged."),
        ("af_pf_ws_session9_sonnet_wallonly", "af_pf_session2",
         {
             "server": {
                 "command": "/usr/bin/python3",
                 "args": ["-S", "{repo}/testing/harness/mcp_prewarm_proxy.py",
                          "--cache", "{repo}/testing/harness/handshake_cache_evolve9.json",
                          "{repo}/.lake/build/bin/lean-mcp-evolve"],
                 # same as session_af_tools_sonnet_wallonly's server env
                 # (evolve_server()'s env WITHOUT LEAN_ENABLE_TOOLS -- unset
                 # means the server's own default of all nine tools).
                 "env": {
                     "LEAN_HINTS": "1",
                     "LEAN_SUGGEST": "1",
                     "LEAN_ENV_V2": "1",
                     "LEAN_AUTO2": "0",
                     "LEAN_AUTO_SEARCH": "0",
                     "LEAN_PRELOAD": "0",
                     "LEAN_IMPORT_ECHO": "0",
                     "LEAN_STEP_TIMEOUT": "30",
                     "LEAN_TRY_TIMEOUT": "15",
                     "LEAN_AUTO_TIMEOUT": "6",
                     "LEAN_OPEN_TIMEOUT": "600",
                     "LEAN_MAX_HEARTBEATS": "200000",
                 },
             },
             "mcp_server_name": "lean",
             "allowed_tools": [
                 "mcp__lean__open", "mcp__lean__build", "mcp__lean__check",
                 "mcp__lean__step", "mcp__lean__try", "mcp__lean__auto_close",
                 "mcp__lean__state", "mcp__lean__rollback", "mcp__lean__verify",
             ],
             "max_turns": 200,
             "workspace": "lake_putnam",
         },
         "PF_WS_SPEC.md (2026-09-09, user request): lean-mcp-evolve with ALL NINE "
         "prover tools (LEAN_ENABLE_TOOLS unset -- the server's own default), behind "
         "the prewarm proxy with handshake_cache_evolve9.json, NO extra_servers, "
         "rerun in the per-problem Lake workspace setting (LEAN_TASK_FILE is set to "
         "the workspace task file automatically by run_eval.py's workspace branch -- "
         "eager open). system_prompt/task_prompt_template kept BYTE-IDENTICAL to "
         "af_pf_session2's (no strategy tail, per A108); only server/allowed_tools/"
         "max_turns/workspace are overridden. Delivery: candidate.lean on PROOF "
         "COMPLETE, unchanged."),
        ("af_pf_ws_session5_sonnet_wallonly", "af_pf_session2",
         {
             "server": {
                 "command": "/usr/bin/python3",
                 "args": ["-S", "{repo}/testing/harness/mcp_prewarm_proxy.py",
                          "--cache", "{repo}/testing/harness/handshake_cache_evolve5.json",
                          "{repo}/.lake/build/bin/lean-mcp-evolve"],
                 # same as session_af_tools_sonnet_wallonly's server env
                 # (evolve_server()'s env WITHOUT LEAN_ENABLE_TOOLS -- unset
                 # means the server's own default of all nine tools).
                 "env": {
                     "LEAN_ENABLE_TOOLS": "step,rollback,state,try,auto_close",
                     "LEAN_HINTS": "1",
                     "LEAN_SUGGEST": "1",
                     "LEAN_ENV_V2": "1",
                     "LEAN_AUTO2": "0",
                     "LEAN_AUTO_SEARCH": "0",
                     "LEAN_PRELOAD": "0",
                     "LEAN_IMPORT_ECHO": "0",
                     "LEAN_STEP_TIMEOUT": "30",
                     "LEAN_TRY_TIMEOUT": "15",
                     "LEAN_AUTO_TIMEOUT": "6",
                     "LEAN_OPEN_TIMEOUT": "600",
                     "LEAN_MAX_HEARTBEATS": "200000",
                 },
             },
             "mcp_server_name": "lean",
             "allowed_tools": [
                 "mcp__lean__step", "mcp__lean__rollback", "mcp__lean__state",
                 "mcp__lean__try", "mcp__lean__auto_close",
             ],
             "max_turns": 200,
             "workspace": "lake_putnam",
         },
         "2026-09-10: the FIVE frozen session tools (the exact af_pf_session2 tool set, Rocq A80/A108) in the workspace setting; replaces af_pf_ws_session9 for the prompt-free evaluation: without file tools the extra tools verify/build/open are traps (verify always fails on the task file's own placeholder because the proof lives in the session candidate; it cost 173 s on the first attempt)."),
        ("af_pf_ws_lean_lsp_mcp_sonnet_wallonly", "af_pf_lean_lsp_mcp",
         {
             "server": {
                 "command": "/usr/bin/python3",
                 "args": ["-S", "{repo}/testing/harness/mcp_prewarm_proxy.py",
                          "uvx", f"lean-lsp-mcp@{LEAN_LSP_MCP_VERSION}"],
                 "env": {"LEAN_PROJECT_PATH": "{workspace}"},
             },
             "mcp_server_name": "leanlsp",
             # extra_servers.final unchanged from af_pf_lean_lsp_mcp: the Rocq
             # sibling delivery mechanism (lean-mcp-submit behind the proxy).
             "extra_servers": {
                 "final": {
                     "command": "/usr/bin/python3",
                     "args": ["-S", "{repo}/testing/harness/mcp_prewarm_proxy.py",
                              "--cache", "{repo}/testing/harness/handshake_cache_submit.json",
                              "{repo}/.lake/build/bin/lean-mcp-submit"],
                 },
             },
             "allowed_tools": [f"mcp__leanlsp__{t}" for t in (LEANLSP_TOOLS or ["TODO_lean_lsp_mcp_tool"])]
                 + ["mcp__final__submit"],
             "max_turns": 200,
             "workspace": "lake_putnam",
             # run_eval.py: rewrite the workspace task file's trailing `sorry`
             # hole to a `by` block after writing it (task.lean and the
             # prompt prefix stay the ORIGINAL term-mode text) -- lean-lsp-
             # mcp's lean_goal/lean_multi_attempt have no tactic state on a
             # term-mode `:= sorry` (see af_lean_lsp_mcp_prompted_sonnet_
             # wallonly's validation notes above); the sibling's environment
             # bridge, in the spirit of A99.
             "workspace_hole_by": True,
         },
         "PF_WS_SPEC.md (2026-09-09, user request): lean-lsp-mcp SOTA sibling "
         f"(pinned v{LEAN_LSP_MCP_VERSION}, matching the captured handshake), "
         "LEAN_PROJECT_PATH pointed at the attempt's own workspace ('{workspace}', "
         "substituted by run_eval.py) instead of the shared LEAN_2026 project. NO "
         "files sidecar. project_task_copy/prefix_prepend DROPPED (af_pf_lean_lsp_"
         "mcp's A99-style bridge is unnecessary: the workspace IS the project lean-"
         "lsp-mcp needs, so its task file already exists there). Delivery kept as "
         "the Rocq sibling mechanism -- extra_servers.final = lean-mcp-submit behind "
         "the proxy, submissions/*.lean graded newest-compiling-first (A76) in the "
         "workspace grading branch. 'workspace_hole_by': true rewrites the workspace "
         "task file's `:= sorry` hole to `:= by\\n  sorry` (task.lean / the prompt "
         "prefix stay the original). system_prompt/task_prompt_template kept BYTE-"
         "IDENTICAL to af_pf_lean_lsp_mcp's."),
    ]
    for lean_id, base_id, overrides, note in PF_WS:
        base = json.loads((OUT_DIR / f"{base_id}.json").read_text())
        base["config_id"] = lean_id
        base["description"] = base["description"] + " | " + note
        base.pop("project_task_copy", None)
        base.pop("prefix_prepend", None)
        base.update(overrides)
        (OUT_DIR / f"{lean_id}.json").write_text(json.dumps(base, indent=1, ensure_ascii=False) + "\n")
        print(f"== {lean_id}  (derived from {base_id}, PF_WS) ==\n"
              f"  wrote {OUT_DIR / (lean_id + '.json')}")

    if LEANLSP_TOOLS is None:
        print("\nNOTE: lean_lsp_mcp_handshake_cache.json not found when this ran -- "
              "lean_lsp_mcp_fair_sonnet's toolset sentence and allowed_tools are TODO "
              "placeholders. Run capture_handshake.py then re-run this script.")
    sys.exit(1 if any_mismatch else 0)


if __name__ == "__main__":
    main()
