#!/usr/bin/env python3
"""Eval runner.

(ported from rocq-mcp-evolve)

For each problem in a manifest, spawns the pinned policy — `claude` CLI in
headless mode, MCP tools only — against the tool-layer config under test,
then verifies the outcome with the correctness gate (gate.py) and appends one
structured record per attempt to <run_dir>/results.jsonl.

Contract with tool servers (all configs): the server must write the current
best complete .lean to $LEAN_WORKDIR/candidate.lean whenever a full check
passes. The gate re-verifies candidate.lean from scratch; the in-session
result is never trusted.

`cfg["workspace"] == "lake_putnam"` arms (AF_TOOLS_SPEC.md sections 2-3) get,
additionally, a fresh per-attempt Lake project at <attempt>/workspace/ that
reuses PROJECT's already-built Mathlib (via an ABSOLUTE packagesDir rewrite —
getting this wrong makes Lake clone and rebuild Mathlib from scratch, see
build_workspace()) and a "files" sidecar the model can write/build/verify
files in; grading there prefers the model's in-place edit of the workspace
task file over the session's candidate.lean (see the gating block in
run_attempt(), and the "artifact" field of each result row).

TWO_ARMS_SPEC.md (2026-09-08): the MAIN MCP server is whatever
cfg["server"]/cfg["mcp_server_name"] say -- not assumed to be
lean-mcp-evolve (e.g. af_compiler_only_prompted_sonnet_wallonly's main
server is the "files" sidecar; af_lean_lsp_mcp_prompted_sonnet_wallonly's is
lean-lsp-mcp). The literal "{workspace}" in any server env VALUE (main or
extra_servers) is substituted with the attempt's workspace dir on
`cfg["workspace"] == "lake_putnam"` arms (e.g.
af_lean_lsp_mcp_prompted_sonnet_wallonly's LEAN_PROJECT_PATH); left
untouched otherwise, so every pre-existing config is unaffected.
"""

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import common
import datasets
import gate

CLAUDE_BIN = os.environ.get("CLAUDE_BIN") or shutil.which("claude") or "/opt/homebrew/bin/claude"
PROJECT = common.PROJECT
# DEVIATION from rocq-mcp-evolve: there is no `rocq_args` / ROCQ_INIT_ARGS /
# ROCQ_COMPILE_ARGS analogue -- Lean has no per-problem project-args concept.
COMPILE_FAILURE_PREFIXES = ("gate:compile_error", "recompile_timeout", "gate_unavailable")

_MATHLIB_REV_RE = re.compile(
    r'\[\[require\]\]\s*\n(?:(?!\[\[).)*?name\s*=\s*"mathlib".*?rev\s*=\s*"([^"]+)"',
    re.DOTALL,
)


def _mathlib_rev(lakefile_toml_text: str) -> str:
    """The `rev` of the `[[require]] name = "mathlib"` block of a
    lakefile.toml (AF_TOOLS_SPEC.md section 2: the per-attempt workspace's
    own lakefile.toml must require the SAME mathlib rev as PROJECT)."""
    m = _MATHLIB_REV_RE.search(lakefile_toml_text)
    if not m:
        raise RuntimeError("could not find a mathlib rev in lakefile.toml")
    return m.group(1)


def build_workspace(adir: Path, rec: dict, content: str) -> tuple[Path, Path]:
    """Fresh <adir>/workspace/ Lake project (AF_TOOLS_SPEC.md section 2):
    lean-toolchain + lake-manifest.json copied from PROJECT (manifest's
    packagesDir rewritten to PROJECT's ABSOLUTE .lake/packages -- SAFETY
    CRITICAL: without this rewrite Lake clones and rebuilds Mathlib into the
    workspace instead of reusing PROJECT's build, a multi-hour, multi-GB
    mistake, verified 2026-09-07), a lakefile.toml requiring that same
    mathlib rev, and Putnam/<problem_id>.lean = the dataset file verbatim.
    Returns (ws_dir, ws_task_path)."""
    ws_dir = adir / "workspace"
    if ws_dir.exists():
        shutil.rmtree(ws_dir)
    ws_dir.mkdir(parents=True)
    proj = Path(PROJECT)

    shutil.copy(proj / "lean-toolchain", ws_dir / "lean-toolchain")

    manifest = json.loads((proj / "lake-manifest.json").read_text())
    packages_dir = str((proj / ".lake" / "packages").resolve())
    manifest["packagesDir"] = packages_dir
    (ws_dir / "lake-manifest.json").write_text(json.dumps(manifest, indent=1))

    rev = _mathlib_rev((proj / "lakefile.toml").read_text())
    (ws_dir / "lakefile.toml").write_text(
        'name = "putnam_ws"\n'
        'defaultTargets = ["Putnam"]\n'
        f'packagesDir = "{packages_dir}"\n'
        "\n"
        "[[require]]\n"
        'name = "mathlib"\n'
        'scope = "leanprover-community"\n'
        f'rev = "{rev}"\n'
        "\n"
        "[[lean_lib]]\n"
        'name = "Putnam"\n'
        'globs = ["Putnam.+"]\n'
    )

    ws_task_path = ws_dir / "Putnam" / f"{rec['problem_id']}.lean"
    ws_task_path.parent.mkdir(parents=True, exist_ok=True)
    ws_task_path.write_text(content)
    return ws_dir, ws_task_path


def rewrite_hole_by(content: str) -> str:
    """PF_WS_SPEC.md `workspace_hole_by` bridge: rewrite a task file's
    trailing `:=\\n  sorry` / `:= sorry` hole to `:= by\\n  sorry` -- only
    that transformation, everything before the final `:=` is untouched.
    `datasets.putnam_prefix` asserts (raises ValueError) that content ends
    with `:=` + optional `by` + `sorry`, exactly the shape this relies on."""
    prefix = datasets.putnam_prefix(content)  # raises if the tail doesn't match
    assert prefix.endswith(":=\n"), prefix[-40:]
    return prefix[:-1] + " by\n  sorry\n"


def _descendants(pid: int) -> list[int]:
    try:
        out = subprocess.run(
            ["pgrep", "-P", str(pid)], capture_output=True, text=True
        ).stdout.split()
    except OSError:
        return []
    ds = []
    for c in out:
        try:
            c = int(c)
        except ValueError:
            continue
        ds.append(c)
        ds.extend(_descendants(c))
    return ds


def kill_attempt_tree(p: subprocess.Popen, log):
    """SIGKILL the spawned CLI, its descendants (MCP server, prover workers),
    and its process group. Logs every step: the 300s-timeout failure observed
    in rocq-mcp-evolve's run baseline_dev60_r1 (attempts alive at ~580s) needs
    a diagnosable kill path."""
    log(f"kill_attempt_tree pid={p.pid} t={time.time():.1f}")
    for d in _descendants(p.pid):
        try:
            os.kill(d, signal.SIGKILL)
        except OSError as e:
            log(f"  kill child {d}: {e!r}")
    for target, fn in [("pg", lambda: os.killpg(os.getpgid(p.pid), signal.SIGKILL)),
                       ("pid", lambda: os.kill(p.pid, signal.SIGKILL))]:
        try:
            fn()
        except OSError as e:
            log(f"  kill {target}: {e!r}")


def build_task(rec):
    """(prefix the agent must extend, theorem name, full task.lean content)."""
    content = (common.MAIN_REPO / rec["path"]).read_text()
    prefix = datasets.putnam_prefix(content)
    return prefix, rec["theorem_name"], content


def aggregate_usage(events, result_event):
    """Token accounting; falls back to per-message events for killed runs."""
    if result_event is not None:
        u = result_event.get("usage", {})
        return {
            "input_tokens": u.get("input_tokens", 0),
            "output_tokens": u.get("output_tokens", 0),
            "cache_read_input_tokens": u.get("cache_read_input_tokens", 0),
            "cache_creation_input_tokens": u.get("cache_creation_input_tokens", 0),
            "total_cost_usd": result_event.get("total_cost_usd"),
            "estimated": False,
        }
    seen_msg, out_tok, in_last = set(), 0, 0
    for ev in events:
        if ev.get("type") != "assistant":
            continue
        msg = ev.get("message", {})
        mid = msg.get("id")
        u = msg.get("usage", {})
        if mid in seen_msg:
            continue
        seen_msg.add(mid)
        out_tok += u.get("output_tokens", 0)
        in_last = max(
            in_last,
            u.get("input_tokens", 0)
            + u.get("cache_read_input_tokens", 0)
            + u.get("cache_creation_input_tokens", 0),
        )
    return {
        "input_tokens": in_last,
        "output_tokens": out_tok,
        "cache_read_input_tokens": 0,
        "cache_creation_input_tokens": 0,
        "total_cost_usd": None,
        "estimated": True,
    }


def _transcript_tool_uses(events):
    """{server: n, ..., "total": n} of tool_use blocks in the stream-json
    transcript (server = the mcp__<server>__ prefix, or "builtin")."""
    out = {}
    for ev in events:
        if ev.get("type") != "assistant":
            continue
        for c in ev.get("message", {}).get("content", []) or []:
            if isinstance(c, dict) and c.get("type") == "tool_use":
                name = c.get("name", "")
                srv = name.split("__")[1] if name.startswith("mcp__") and name.count("__") >= 2 else "builtin"
                out[srv] = out.get(srv, 0) + 1
    out["total"] = sum(out.values())
    return out


def run_attempt(cfg, rec, rep, run_dir, run_id, dry_run=False):
    prefix, thm, content = build_task(rec)
    aid = f"{rec['problem_id']}__rep{rep}"
    # Optional sibling bridge (section 6 of PORT_SPEC.md, A99-in-spirit): a
    # copy of the task file placed inside the real Lean project so an
    # LSP-backed sibling tool (lean-lsp-mcp) can open/diagnose it, plus a
    # one-line comment prepended to BOTH the prefix and task.lean so the
    # gate's reference and what the agent sees are one file.
    project_copy_path = None
    if cfg.get("project_task_copy"):
        task_rel = cfg["project_task_copy"].format(aid=aid)
        project_copy_path = Path(PROJECT) / task_rel
        if cfg.get("prefix_prepend"):
            prepend = cfg["prefix_prepend"].format(task_rel=task_rel)
            prefix = prepend + prefix
            content = prepend + content
    elif cfg.get("prefix_prepend"):
        prefix = cfg["prefix_prepend"] + prefix
        content = cfg["prefix_prepend"] + content

    adir = run_dir / "attempts" / aid
    work = adir / "work"
    work.mkdir(parents=True, exist_ok=True)
    server_log = adir / "server.jsonl"
    # A93 (rocq-mcp-evolve): a crashed or duplicated predecessor attempt may
    # have left grading artifacts behind; this attempt must never be graded
    # on them.
    for stale in [work / "candidate.lean", server_log, adir / "gate_reject.txt"]:
        stale.unlink(missing_ok=True)
    if (work / "submissions").exists():
        shutil.rmtree(work / "submissions")
    bucket = datasets.bucket_of(rec)
    meta = {
        "run_id": run_id,
        "config_id": cfg["config_id"],
        "problem_id": rec["problem_id"],
        "difficulty": bucket,
        "source": rec["source"],
        "rep": rep,
        "agent_id": aid,
    }
    # AF_TOOLS_SPEC.md section 2: a per-problem Lake project the model can
    # read/write/build files in, sharing PROJECT's already-built Mathlib.
    is_workspace = cfg.get("workspace") == "lake_putnam"
    ws_dir = ws_task_path = None
    if is_workspace:
        ws_dir, ws_task_path = build_workspace(adir, rec, content)
        if cfg.get("workspace_hole_by"):
            # PF_WS_SPEC.md: an LSP-backed sibling (lean-lsp-mcp) has no
            # tactic state to query on a term-mode `:= sorry`; rewrite the
            # WORKSPACE COPY only -- task.lean (written below) and the
            # prompt's {prefix} slot stay the original term-mode text, and
            # the gate always compares the submission to that unmodified
            # reference.
            ws_task_path.write_text(rewrite_hole_by(content))
        ws_written = ws_task_path.read_text() if ws_task_path is not None else None

    server_env = {
        # toolchain env computed once per run (deviation 16): LEAN_PATH,
        # LEAN_SYSROOT, PATH as `lake env` exports them in PROJECT
        **common.toolchain_env(PROJECT),
        "HOME": os.environ.get("HOME", ""),
        "LEAN_WORKDIR": str(work),
        "LEAN_LOG_FILE": str(server_log),
        "LEAN_LOG_META": json.dumps(meta),
        "LEAN_TASK_FILE": str(ws_task_path) if is_workspace else str(adir / "task.lean"),
        "LEAN_PROJECT_ROOT": str(ws_dir) if is_workspace else PROJECT,
    }
    if is_workspace:
        # consumed by the "files" sidecar (extra_servers below); harmless
        # extra var for the main server itself.
        server_env["LEAN_WORKSPACE"] = str(ws_dir)
    server_env.update(cfg["server"].get("env", {}))
    server_cmd = cfg["server"]["command"].replace("{repo}", str(common.MAIN_REPO))
    server_args = [a.replace("{repo}", str(common.MAIN_REPO)) for a in cfg["server"].get("args", [])]
    # TWO_ARMS_SPEC.md: "{workspace}" in any server env VALUE is substituted
    # with the attempt's workspace dir (arms with cfg["workspace"] ==
    # "lake_putnam" only -- e.g. af_lean_lsp_mcp_prompted_sonnet_wallonly's
    # LEAN_PROJECT_PATH). Arms without a workspace never contain the
    # placeholder, so this is a no-op for every other config.
    ws_for_sub = str(ws_dir) if is_workspace else None

    def _env_with_ws(env):
        if ws_for_sub is None:
            return env
        return {k: (v.replace("{workspace}", ws_for_sub) if isinstance(v, str) else v)
                for k, v in env.items()}

    # The main MCP server: whatever cfg["server"]/cfg["mcp_server_name"] say
    # -- NOT assumed to be lean-mcp-evolve (e.g. af_compiler_only_prompted_
    # sonnet_wallonly's main server is the "files" sidecar, and
    # af_lean_lsp_mcp_prompted_sonnet_wallonly's is lean-lsp-mcp). The
    # LEAN_TASK_FILE/LEAN_PROJECT_ROOT/LEAN_WORKDIR/etc. env above is always
    # provided regardless -- harmless for servers that ignore it.
    mcp_cfg = {
        "mcpServers": {
            cfg.get("mcp_server_name", "lean"): {
                "command": server_cmd,
                "args": server_args,
                "env": _env_with_ws(server_env),
            }
        }
    }
    # additional MCP servers (e.g. the submit sidecar for external-tool
    # configs); {repo} and the standard LEAN_* env are provided
    for name, srv in cfg.get("extra_servers", {}).items():
        mcp_cfg["mcpServers"][name] = {
            "command": srv["command"].replace("{repo}", str(common.MAIN_REPO)),
            "args": [a.replace("{repo}", str(common.MAIN_REPO)) for a in srv.get("args", [])],
            "env": _env_with_ws({**server_env, **srv.get("env", {})}),
        }
    (adir / "mcp.json").write_text(json.dumps(mcp_cfg, indent=1))
    # {task_file}: the theorem's path relative to the workspace root (arms with
    # a per-problem project tell the model where its file lives); {problem_id}.
    task_file_rel = (str(ws_task_path.relative_to(ws_dir)) if is_workspace
                     else f"{rec['problem_id']}.lean")
    task_prompt = cfg["task_prompt_template"].format(
        prefix=prefix, statement=rec.get("statement", ""),
        task_file=task_file_rel, problem_id=rec["problem_id"])
    (adir / "task_prefix.lean").write_text(prefix)
    (adir / "task.lean").write_text(content)
    if project_copy_path is not None:
        project_copy_path.parent.mkdir(parents=True, exist_ok=True)
        project_copy_path.write_text(content)

    if dry_run:
        # section 6 of AF_TOOLS_SPEC.md: build everything a real attempt
        # would need (attempt dir, workspace, mcp.json, the prompt) and
        # stop -- no claude CLI, no gate.
        (adir / "prompt.txt").write_text(task_prompt)
        return {
            "dry_run": True,
            "problem_id": rec["problem_id"],
            "rep": rep,
            "attempt_dir": str(adir),
            "workspace_dir": str(ws_dir) if is_workspace else None,
            "mcp_json": str(adir / "mcp.json"),
            "prompt_file": str(adir / "prompt.txt"),
        }

    cmd = [
        CLAUDE_BIN,
        "-p", task_prompt,
        "--model", cfg["model"],
        *(["--system-prompt", cfg["system_prompt"]]
          if cfg.get("system_prompt") else []),
        "--strict-mcp-config", "--mcp-config", str(adir / "mcp.json"),
        "--tools", "",
        "--allowedTools", ",".join(cfg["allowed_tools"]),
        "--max-turns", str(cfg["max_turns"]),
        "--output-format", "stream-json", "--verbose",
    ]
    t0 = time.time()
    timed_out = False
    kill_log_path = adir / "kill.log"

    def klog(msg):
        with open(kill_log_path, "a") as kf:
            kf.write(msg + "\n")

    try:
        with open(adir / "transcript.jsonl", "w") as tf, open(adir / "stderr.log", "w") as ef:
            # Launch; a missing CLI binary is infrastructure (the claude CLI
            # self-updates and its /opt/homebrew/bin symlink was absent for a
            # few minutes on 2026-09-08, turning 100 slots into harness_error
            # rows): park and retry rather than record a verdict (429 precedent).
            for _try in range(30):
                try:
                    p = subprocess.Popen(
                        cmd,
                        stdout=tf,
                        stderr=ef,
                        stdin=subprocess.DEVNULL,
                        cwd=(ws_dir if is_workspace else adir),
                        start_new_session=True,
                    )
                    break
                except FileNotFoundError as e:
                    klog(f"claude CLI not launchable ({e!r}); parking 60s (try {_try + 1}/30)")
                    time.sleep(60)
            else:
                raise FileNotFoundError(f"claude CLI not launchable after 30 tries: {CLAUDE_BIN}")
            # WALL-CLOCK deadline watchdog. p.wait(timeout)/threading.Timer use
            # the monotonic clock, which does not advance while macOS sleeps —
            # an attempt spanning a laptop sleep would blow way past its
            # budget. Poll wall-clock time instead; the sleep gap then counts
            # against the attempt and it is killed on wake.
            watchdog_fired = threading.Event()
            slept = threading.Event()
            stop_wd = threading.Event()
            deadline_wall = t0 + cfg["attempt_timeout_s"]
            m0 = time.monotonic()

            def watchdog():
                while not stop_wd.wait(2.0):
                    drift = (time.time() - t0) - (time.monotonic() - m0)
                    if drift > 5.0 and not slept.is_set():
                        slept.set()
                        klog(f"machine slept during attempt: wall-mono drift {drift:.0f}s")
                    if time.time() > deadline_wall:
                        watchdog_fired.set()
                        klog(f"wall-clock watchdog fired at +{time.time()-t0:.1f}s")
                        kill_attempt_tree(p, klog)
                        return

            wd = threading.Thread(target=watchdog, daemon=True)
            wd.start()
            try:
                p.wait(timeout=cfg["attempt_timeout_s"] + 15)
            except subprocess.TimeoutExpired:
                klog(f"p.wait timeout at +{time.time()-t0:.1f}s")
                kill_attempt_tree(p, klog)
                p.wait()
            finally:
                stop_wd.set()
            timed_out = timed_out or watchdog_fired.is_set() or (time.time() > deadline_wall)
    finally:
        if project_copy_path is not None:
            project_copy_path.unlink(missing_ok=True)
    wall_s = time.time() - t0
    if wall_s > cfg["attempt_timeout_s"] + 30:
        klog(f"ANOMALY: attempt outlived timeout: wall={wall_s:.1f}s timed_out={timed_out}")

    events = common.read_jsonl(adir / "transcript.jsonl")
    result_event = next((e for e in reversed(events) if e.get("type") == "result"), None)
    # A83 (rocq-mcp-evolve): quota poisoning — a 429/session-limit result
    # invalidates the attempt (infrastructure, not model). Park the
    # transcript, wait out the window, and redo the SAME slot.
    _re = result_event or {}
    _dead_stream = (result_event is None
                    and not any(e.get("type") == "assistant" for e in events)
                    and not any(e.get("type") == "system"
                                and e.get("subtype") == "thinking_tokens"
                                for e in events))
    if (_re.get("api_error_status") == 429
            or "session limit" in str(_re.get("result", "")).lower()
            or _dead_stream):
        import shutil as _sh
        _sh.move(adir / "transcript.jsonl",
                 adir / f"transcript.poisoned.{int(time.time())}.jsonl")
        klog("quota-poisoned or dead stream (zero assistant events); parking 20min then redoing this slot")
        time.sleep(1200)
        return run_attempt(cfg, rec, rep, run_dir, run_id, dry_run=dry_run)
    usage = aggregate_usage(events, result_event)
    denials = (result_event or {}).get("permission_denials", [])

    server_records = common.read_jsonl(server_log)
    calls = [r for r in server_records if r.get("kind") == "tool_call"]
    prover_ms = sum(r.get("prover_ms", 0.0) for r in calls)
    tool_durs = [round(r.get("dur_ms", 0.0), 1) for r in calls]

    candidate_path = work / "candidate.lean"
    subs_dir = work / "submissions"
    reference = adir / "task.lean"
    artifact = None
    if is_workspace:
        # AF_TOOLS_SPEC.md section 3: deliverable order is (a) the workspace
        # task file, IF the model edited it in place, (b) the session's
        # candidate.lean, (c) no_candidate. If (a) exists but is rejected and
        # (b) exists, (b) is also graded and an accepting verdict from
        # EITHER artifact wins (recorded in "artifact" below). Helper lemmas
        # in extra workspace files cannot be imported by the task file (the
        # reference check locks its imports) -- the delivered proof must be
        # self-contained in Putnam/<id>.lean or in candidate.lean.
        gate_res = None
        if ws_task_path is not None and ws_task_path.exists():
            ws_text = ws_task_path.read_text()
            # "edited by the model" = differs from what the HARNESS wrote there
            # (the hole-rewritten copy when workspace_hole_by is set, else the
            # original); comparing against the original mislabelled every
            # no-submission attempt of the lean-lsp-mcp arm as
            # forbidden_token:sorry and gated the placeholder file needlessly
            # (2026-09-10, run putnam60_pf_ws_lean_lsp_mcp).
            if ws_text != ws_written:
                gate_res = gate.check(ws_text, prefix, thm,
                                      reference=reference, project=ws_dir)
                if gate_res["solved"]:
                    artifact = "workspace_file"
        # PF_WS_SPEC.md item (a): the lean-lsp-mcp workspace arm delivers via
        # the Rocq sibling mechanism (submit -> <work>/submissions/*.lean),
        # not a session candidate.lean -- graded newest-first with the A76
        # rule (mirroring the non-workspace sibling branch below), BEFORE
        # the candidate.lean fallback. Harmless for every other workspace
        # arm: without a "final" submit server, submissions/ never exists.
        if ((gate_res is None or not gate_res["solved"])
                and subs_dir.exists() and any(subs_dir.glob("*.lean"))):
            gate_res_s = None
            for sub in sorted(subs_dir.glob("*.lean"), reverse=True):
                r = gate.check(sub.read_text(), prefix, thm,
                               reference=reference, project=ws_dir)
                if gate_res_s is None:
                    gate_res_s = r          # newest verdict is the default
                if not str(r.get("reason") or "").startswith(COMPILE_FAILURE_PREFIXES):
                    gate_res_s = r
                    break
            if gate_res_s["solved"]:
                gate_res = gate_res_s
                artifact = "submission"
            elif gate_res is None:
                gate_res = gate_res_s
        if (gate_res is None or not gate_res["solved"]) and candidate_path.exists():
            gate_res_b = gate.check(candidate_path.read_text(), prefix, thm,
                                    reference=reference, project=ws_dir)
            if gate_res_b["solved"]:
                gate_res = gate_res_b
                artifact = "candidate"
            elif gate_res is None:
                gate_res = gate_res_b
        if gate_res is None:
            gate_res = {"solved": False, "reason": "no_candidate", "axioms": None,
                        "recompile_s": None, "detail": None}
    elif subs_dir.exists() and any(subs_dir.glob("*.lean")):
        # A76 parity (rocq-mcp-evolve, external-submit arms): the artifact is
        # the NEWEST submission that compiles — mirroring baseline's
        # last-exit-0 semantics — so a later broken submit cannot clobber a
        # good one.
        gate_res = None
        for sub in sorted(subs_dir.glob("*.lean"), reverse=True):
            r = gate.check(sub.read_text(), prefix, thm, reference=reference, project=PROJECT)
            if gate_res is None:
                gate_res = r          # newest verdict is the default
            if not str(r.get("reason") or "").startswith(COMPILE_FAILURE_PREFIXES):
                gate_res = r
                break
    elif candidate_path.exists():
        gate_res = gate.check(candidate_path.read_text(), prefix, thm,
                              reference=reference, project=PROJECT)
    else:
        gate_res = {"solved": False, "reason": "no_candidate", "axioms": None,
                    "recompile_s": None, "detail": None}

    record = {
        "ts": t0,
        "run_id": run_id,
        "config_id": cfg["config_id"],
        "model": cfg["model"],
        "problem_id": rec["problem_id"],
        "source": rec["source"],
        "difficulty": bucket,
        "source_tier": rec.get("source_tier"),
        "rep": rep,
        "seed": rep,
        "solved": gate_res["solved"],
        "reject_reason": gate_res["reason"],
        "artifact": artifact,
        "gate": {k: v for k, v in gate_res.items() if k != "detail"},
        "wall_s": round(wall_s, 2),
        "attempt_timed_out": timed_out,
        "machine_slept": slept.is_set(),
        "num_turns": (result_event or {}).get("num_turns"),
        "stop_reason": (result_event or {}).get("stop_reason"),
        "duration_ms": (result_event or {}).get("duration_ms"),
        "duration_api_ms": (result_event or {}).get("duration_api_ms"),
        "usage": usage,
        "total_cost_usd": usage.get("total_cost_usd"),
        "tool_calls": len(calls),
        # every tool_use block the model emitted, per MCP server name, from the
        # transcript -- servers that do not write LEAN_LOG_FILE (lean-lsp-mcp)
        # are invisible to `tool_calls`/`tool_dur_ms` above (deviation 21)
        "tool_uses_transcript": _transcript_tool_uses(events),
        "prover_ms_total": round(prover_ms, 1),
        "tool_dur_ms": tool_durs,
        "permission_denials": len(denials),
        "result_text": ((result_event or {}).get("result") or "")[:200],
        "attempt_dir": str(adir.relative_to(common.LOGS)),
    }
    if gate_res.get("detail"):
        (adir / "gate_reject.txt").write_text(gate_res["detail"])
    common.append_jsonl(run_dir / "results.jsonl", record)
    return record


def _binary_sha256(path: Path):
    if not path.exists():
        return None
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", required=True)
    ap.add_argument("--manifest", required=True)
    ap.add_argument("--reps", type=int, default=1)
    ap.add_argument("--parallel", type=int, default=4)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--run-id", default=None)
    ap.add_argument("--buckets", default=None, help="comma-separated difficulty filter")
    ap.add_argument("--dry-run", action="store_true",
                     help="build the attempt dir/workspace/mcp.json/prompt.txt for each "
                          "todo record and stop (no claude CLI, no gate) -- AF_TOOLS_SPEC.md "
                          "section 6")
    args = ap.parse_args()

    cfg = common.load_config(args.config)
    problems = common.load_manifest(args.manifest)
    if args.buckets:
        keep = set(args.buckets.split(","))
        problems = [p for p in problems if p["difficulty"] in keep]
    if args.limit:
        problems = problems[: args.limit]

    run_id = args.run_id or f"{cfg['config_id']}__{Path(args.manifest).stem}__{time.strftime('%m%d_%H%M%S')}"
    run_dir = common.LOGS / "runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)

    done = {(r["problem_id"], r["rep"]) for r in common.read_jsonl(run_dir / "results.jsonl")}
    todo = [
        (rec, rep)
        for rep in range(args.reps)
        for rec in problems
        if (rec["problem_id"], rep) not in done
    ]

    # repo is not git; record "n/a" plus a hash of the built binary instead
    # of a commit sha (DEVIATION from rocq-mcp-evolve, which recorded
    # `git rev-parse HEAD`; see testing/README.md).
    git_rev = "n/a"
    binary_sha256 = _binary_sha256(common.MAIN_REPO / ".lake" / "build" / "bin" / "lean-mcp-evolve")
    run_meta = {
        "run_id": run_id,
        "config": cfg,
        "manifest": args.manifest,
        "n_problems": len(problems),
        "reps": args.reps,
        "parallel": args.parallel,
        "git_rev": git_rev,
        "binary_sha256_lean_mcp_evolve": binary_sha256,
        "started": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "host": {
            "platform": platform.platform(),
            "machine": platform.machine(),
            "cpu_count": os.cpu_count(),
        },
        "claude_bin": CLAUDE_BIN,
        "resumed_skipping": len(done),
    }
    (run_dir / "run_meta.json").write_text(json.dumps(run_meta, indent=1))
    print(f"[run {run_id}] {len(todo)} attempts (skipping {len(done)} done), "
          f"parallel={args.parallel}, model={cfg['model']}", flush=True)

    t0 = time.time()
    n_done = n_solved = 0
    with ThreadPoolExecutor(max_workers=args.parallel) as ex:
        futs = {
            ex.submit(run_attempt, cfg, rec, rep, run_dir, run_id, args.dry_run): (rec, rep)
            for rec, rep in todo
        }
        for fut in as_completed(futs):
            rec, rep = futs[fut]
            try:
                r = fut.result()
                n_done += 1
                if args.dry_run:
                    print(
                        f"  [{n_done}/{len(todo)}] DRY-RUN {r['problem_id']} rep{rep} "
                        f"attempt_dir={r['attempt_dir']} workspace_dir={r['workspace_dir']} "
                        f"mcp_json={r['mcp_json']} prompt_file={r['prompt_file']}",
                        flush=True,
                    )
                    continue
                n_solved += r["solved"]
                print(
                    f"  [{n_done}/{len(todo)}] {r['problem_id']} rep{rep} "
                    f"{'SOLVED' if r['solved'] else 'no (' + str(r['reject_reason']) + ')'} "
                    f"turns={r['num_turns']} calls={r['tool_calls']} "
                    f"wall={r['wall_s']}s cost=${r['total_cost_usd'] or 0:.4f}",
                    flush=True,
                )
            except Exception as e:
                n_done += 1
                print(f"  [{n_done}/{len(todo)}] {rec['problem_id']} rep{rep} HARNESS-ERROR {e!r}", flush=True)
                common.append_jsonl(
                    run_dir / "results.jsonl",
                    {
                        "ts": time.time(), "run_id": run_id, "config_id": cfg["config_id"],
                        "problem_id": rec["problem_id"], "difficulty": datasets.bucket_of(rec),
                        "source": rec["source"], "rep": rep, "solved": False,
                        "reject_reason": f"harness_error:{type(e).__name__}",
                        "harness_error": repr(e),
                    },
                )
    print(f"[run {run_id}] done: {n_solved}/{n_done} solved in {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
