#!/usr/bin/env python3
"""Capture an MCP server's initialize + tools/list handshake into a cache
file, in the exact shape mcp_prewarm_proxy.py expects (see
lean_lsp_mcp_handshake_cache.json / rocq-mcp-evolve's
harness/rocq_mcp_handshake_cache.json for the shape this mirrors):

    {"initialize": <initialize result>, "tools": <tools/list result>}

(ported from rocq-mcp-evolve; rocq-mcp-evolve captured this cache by hand /
out-of-band — this script is new, since the Lean port needs to (re)capture it
for lean-lsp-mcp instead of rocq-mcp)

Usage: python3 capture_handshake.py <server-command> [args...] [--out PATH]

Example (from testing/harness/):
    LEAN_PROJECT_PATH=/Users/jviennot/Documents/Cours/LEAN_2026 \\
        python3 capture_handshake.py uvx lean-lsp-mcp
"""

import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_OUT = os.path.join(HERE, "lean_lsp_mcp_handshake_cache.json")


def send(proc, msg):
    proc.stdin.write(json.dumps(msg) + "\n")
    proc.stdin.flush()


def recv(proc, want_id, timeout_s=90):
    t0 = time.time()
    while time.time() - t0 < timeout_s:
        line = proc.stdout.readline()
        if not line:
            if proc.poll() is not None:
                raise RuntimeError(f"server exited (code {proc.returncode}) before id={want_id}")
            continue
        line = line.strip()
        if not line:
            continue
        try:
            m = json.loads(line)
        except json.JSONDecodeError:
            continue
        if m.get("id") == want_id:
            return m
    raise TimeoutError(f"no response with id={want_id} within {timeout_s}s")


def main():
    argv = sys.argv[1:]
    out_path = DEFAULT_OUT
    if "--out" in argv:
        i = argv.index("--out")
        out_path = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
    if not argv:
        print("usage: capture_handshake.py <server-command> [args...] [--out PATH]",
              file=sys.stderr)
        sys.exit(2)

    proc = subprocess.Popen(
        argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=sys.stderr,
        text=True, bufsize=1, env=os.environ.copy(),
    )
    try:
        send(proc, {"jsonrpc": "2.0", "id": 1, "method": "initialize",
                     "params": {"protocolVersion": "2025-11-25", "capabilities": {},
                                "clientInfo": {"name": "capture-handshake", "version": "1"}}})
        init_resp = recv(proc, 1)
        if "error" in init_resp:
            print(f"initialize failed: {init_resp['error']}", file=sys.stderr)
            sys.exit(1)
        init_result = init_resp["result"]
        send(proc, {"jsonrpc": "2.0", "method": "notifications/initialized"})
        send(proc, {"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})
        tools_resp = recv(proc, 2)
        if "error" in tools_resp:
            print(f"tools/list failed: {tools_resp['error']}", file=sys.stderr)
            sys.exit(1)
        tools_result = tools_resp["result"]
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()

    cache = {"initialize": init_result, "tools": tools_result}
    with open(out_path, "w") as f:
        json.dump(cache, f, indent=1)
    names = [t["name"] for t in tools_result.get("tools", [])]
    print(f"wrote {out_path}: {len(names)} tools: {', '.join(names)}")


if __name__ == "__main__":
    main()
