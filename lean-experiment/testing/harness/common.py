"""Shared paths, config loading, and JSONL helpers for the eval harness.

(ported from rocq-mcp-evolve)
"""

import json
import os
import threading
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent  # .../lean-mcp-evolve/testing
# DEVIATION from rocq-mcp-evolve: there, REPO was the whole harness repo and
# WORKROOT = REPO.parent held sibling dataset checkouts (_opam/, miniF2F-rocq/).
# Here everything (server sources, dataset/, .lake build outputs, lakefile.toml)
# lives in ONE repo with testing/ as a subdirectory, so we additionally need the
# true project root for those paths.
MAIN_REPO = REPO.parent  # .../lean-mcp-evolve
ELAN_BIN = Path(os.path.expanduser("~/.elan/bin"))  # was OPAM_BIN
LOGS = REPO / "logs"
CONFIGS = REPO / "configs"
MANIFESTS = REPO / "data" / "manifests"

_write_lock = threading.Lock()


def load_config(name_or_path: str) -> dict:
    p = Path(name_or_path)
    if not p.exists():
        p = CONFIGS / f"{name_or_path}.json"
    cfg = json.loads(p.read_text())
    assert "config_id" in cfg and "server" in cfg and "model" in cfg, p
    return cfg


def load_manifest(name_or_path: str) -> list[dict]:
    p = Path(name_or_path)
    if not p.exists():
        p = MANIFESTS / f"{name_or_path}.jsonl"
    return [json.loads(l) for l in p.read_text().splitlines() if l.strip()]


def append_jsonl(path: Path, record: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    with _write_lock:
        with open(path, "a") as f:
            f.write(json.dumps(record, sort_keys=True) + "\n")


def read_jsonl(path: Path) -> list[dict]:
    if not Path(path).exists():
        return []
    out = []
    # errors="replace": the Lean server may emit truncated UTF-8 sequences in
    # logged agent text; never let one bad byte lose a whole attempt record
    for line in Path(path).read_text(errors="replace").splitlines():
        line = line.strip()
        if line:
            try:
                out.append(json.loads(line))
            except json.JSONDecodeError:
                pass  # torn write from a killed process; skip
    return out


PROJECT = os.environ.get("LEAN_EVAL_PROJECT", "/Users/jviennot/Documents/Cours/LEAN_2026")

_toolchain_env_cache: dict = {}


def toolchain_env(project: str = PROJECT) -> dict:
    """`LEAN_PATH`, `LEAN_SYSROOT`, `PATH` (toolchain bin first) as `lake env`
    exports them in `project`, computed ONCE per process (deviation 16). Passing
    them to every server/gate process makes the binaries' own `lake env`
    bootstrap (`LeanMcpEvolve.Reexec`) a no-op: each `lake env printenv` call
    took ~9 s under memory pressure and the three of them pushed the MCP
    handshake past the claude CLI's startup deadline (medium5 test run,
    2026-09-06). Falls back to elan-bin-only PATH if lake fails."""
    if project in _toolchain_env_cache:
        return _toolchain_env_cache[project]
    import subprocess
    out = {}
    try:
        p = subprocess.run(["lake", "env", "env"], cwd=project, capture_output=True, text=True,
                           timeout=300, env={**os.environ, "PATH": f"{ELAN_BIN}:{os.environ.get('PATH', '')}"})
        if p.returncode == 0:
            for line in p.stdout.splitlines():
                k, _, v = line.partition("=")
                if k in ("LEAN_PATH", "LEAN_SYSROOT", "PATH", "LEAN_SRC_PATH"):
                    out[k] = v
    except (OSError, subprocess.TimeoutExpired):
        pass
    if "PATH" not in out:
        out["PATH"] = f"{ELAN_BIN}:/usr/bin:/bin:/usr/sbin:/sbin"
    else:
        out["PATH"] = f"{out['PATH']}:/usr/bin:/bin:/usr/sbin:/sbin"
    _toolchain_env_cache[project] = out
    return out


def prover_env() -> dict:
    """Environment for processes that must find `lake`/`lean` and the project's
    oleans: elan bin first, plus the project's toolchain variables."""
    env = dict(os.environ)
    env.update(toolchain_env())
    return env
