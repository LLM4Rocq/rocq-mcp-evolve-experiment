#!/usr/bin/env python3
"""Instant-handshake MCP proxy (fair-integration fix, ported from
rocq-mcp-evolve's REPORT SOTA section).

(ported from rocq-mcp-evolve)

The claude CLI only exposes an MCP server's tools from the agent's first
turn if the server completes the handshake within a short synchronous
window. Our in-process Lean servers answer in milliseconds; lean-lsp-mcp's
Python stack takes noticeably longer (LSP startup + `lake` warmup), so
without this proxy most comparison attempts would start with its tools
invisible.

This proxy answers the handshake INSTANTLY from a captured cache
(harness/lean_lsp_mcp_handshake_cache.json, written by capture_handshake.py)
while the real server warms up behind it; tool calls are forwarded verbatim
(queued until the child is ready). Transparent: same tools, same behavior,
only the startup race removed.

Usage (as the MCP server command):
    python3 -S mcp_prewarm_proxy.py <real-server-command> [args...]
"""

import json
import os
import subprocess
import sys
import threading

CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                     "lean_lsp_mcp_handshake_cache.json")
PROXY_INIT_ID = "__proxy_init__"
PROXY_TOOLS_ID = "__proxy_tools__"


def out(msg):
    sys.stdout.write(json.dumps(msg) + "\n")
    sys.stdout.flush()


def main():
    # `--cache PATH` (first two args) selects the handshake cache; default =
    # the lean-lsp-mcp cache next to this file. The Lean port also puts this
    # proxy in front of its OWN servers (README deviation 16): their 150 MB
    # binaries need ~4 s to start and the `lake env` bootstrap ~10-30 s under
    # memory pressure, and the claude CLI marked such servers "failed"
    # (medium5 test run, 2026-09-06: 4/5 attempts started with no tools).
    cache_path = CACHE
    argv = sys.argv[1:]
    if len(argv) >= 2 and argv[0] == "--cache":
        cache_path, argv = argv[1], argv[2:]
    with open(cache_path) as f:
        cache = json.load(f)

    child = subprocess.Popen(
        argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
        stderr=sys.stderr, text=True, bufsize=1)

    child_ready = threading.Event()
    child_lock = threading.Lock()

    def to_child(m):
        with child_lock:
            child.stdin.write(json.dumps(m) + "\n")
            child.stdin.flush()

    # proxy's own handshake with the child, started immediately
    to_child({"jsonrpc": "2.0", "id": PROXY_INIT_ID, "method": "initialize",
              "params": {"protocolVersion":
                         cache["initialize"].get("protocolVersion",
                                                 "2025-11-25"),
                         "capabilities": {},
                         "clientInfo": {"name": "prewarm-proxy",
                                        "version": "1"}}})

    def pump_child():
        for line in child.stdout:
            try:
                m = json.loads(line)
            except json.JSONDecodeError:
                continue
            if m.get("id") == PROXY_INIT_ID:
                to_child({"jsonrpc": "2.0",
                          "method": "notifications/initialized"})
                child_ready.set()
                continue
            if m.get("id") == PROXY_TOOLS_ID:
                continue
            out(m)  # responses + notifications flow straight through

    threading.Thread(target=pump_child, daemon=True).start()

    for line in sys.stdin:
        try:
            m = json.loads(line)
        except json.JSONDecodeError:
            continue
        meth = m.get("method", "")
        if meth == "initialize":
            res = dict(cache["initialize"])
            req_pv = (m.get("params") or {}).get("protocolVersion")
            if req_pv:
                res["protocolVersion"] = req_pv
            out({"jsonrpc": "2.0", "id": m.get("id"), "result": res})
        elif meth == "notifications/initialized":
            pass  # proxy already initialized the child
        elif meth == "tools/list":
            out({"jsonrpc": "2.0", "id": m.get("id"),
                 "result": cache["tools"]})
        elif meth in ("prompts/list", "resources/list"):
            key = "prompts" if "prompts" in meth else "resources"
            out({"jsonrpc": "2.0", "id": m.get("id"), "result": {key: []}})
        else:
            child_ready.wait(timeout=60)
            to_child(m)

    # kill the child AND its descendants: the Lean binaries may re-exec
    # themselves through `lake env` (LeanMcpEvolve.Reexec), leaving a
    # grandchild that a plain child.kill() would orphan (16 GB each on
    # Mathlib tasks; observed leaks 2026-09-07).
    def _descendants(pid):
        try:
            kids = subprocess.run(["pgrep", "-P", str(pid)], capture_output=True,
                                  text=True).stdout.split()
        except OSError:
            return []
        out_ = []
        for k in kids:
            try:
                k = int(k)
            except ValueError:
                continue
            out_.append(k)
            out_.extend(_descendants(k))
        return out_
    for d in _descendants(child.pid):
        try:
            os.kill(d, 9)
        except OSError:
            pass
    child.kill()


if __name__ == "__main__":
    main()
