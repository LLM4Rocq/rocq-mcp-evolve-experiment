/-
`lean-mcp-evolve`'s entry point (docs/PLAN.md §4/§5, phase 3 deliverable 2).
Port of `prototype-python/src/lean_mcp_evolve/session_server.py`'s `main`:
parse `LEAN_ENABLE_TOOLS` (comma-separated; default = all nine tools), filter
`Session.allTools`, and serve them over MCP stdio.

Session state: a single `IO.Ref (Option Driver.Session)` created here (in
`main`) and threaded into `Session.allTools`, rather than a top-level
`initialize`/`builtin_initialize` ref -- see `Session.lean`'s module doc.
Every `Lean.initSearchPath` call this process needs happens lazily, per
project root, inside `Driver.openFile`/`Driver.diagnoseFile`/`Verify.verify`
(`Driver.initSearchPath`), so `main` itself does not call it: the executable
works both `lake env`-wrapped inside a project (where `LEAN_PATH` is already
set by the wrapper) and invoked directly (where `Driver.initSearchPath`
discovers it per-root via `lake env printenv LEAN_PATH`, docs/PLAN.md §3).
-/
import LeanMcpEvolve.Session
import LeanMcpEvolve.Reexec

open LeanMcpEvolve
open Lean (Json toJson)

/-- `LEAN_PREWARM=0` disables both prewarm triggers below (default: enabled).
-/
def prewarmEnabled : IO Bool := do
  match ← IO.getEnv "LEAN_PREWARM" with
  | some v => return v ≠ "0"
  | none => return true

/-- `LEAN_PREWARM_IMPORTS`, a comma-separated module list (e.g. `Mathlib`),
parsed the same way `LEAN_ENABLE_TOOLS` is. -/
def prewarmImportsEnv : IO (List String) := do
  match ← IO.getEnv "LEAN_PREWARM_IMPORTS" with
  | some raw =>
    return (raw.splitOn ",").filterMap fun x =>
      let t := Hints.trimStr x
      if t == "" then none else some t
  | none => return []

/-- Kick off the background header-only prewarm task (README "Excluding
Mathlib import time from attempt budgets") for `LEAN_PREWARM_IMPORTS`, when
that's explicitly set and non-empty. No-op when `LEAN_PREWARM=0` or when it's
unset/empty.

Only `LEAN_PREWARM_IMPORTS` starts a SEPARATE dedicated header-prewarm task
here -- a bare `LEAN_TASK_FILE` preset (no explicit import list) does NOT
also get one: `Session.startEagerOpen`'s own background task (started right
after this returns, also before `initialize` is answered, also on its own
dedicated thread) already loads that exact header itself as the first thing
`Driver.openFile` does, tagged `prewarm: true` via its own `prewarm := true`
argument (see `Driver.openFile`'s doc comment) -- so the "start loading
before the handshake" requirement is met either way, without a SECOND
dedicated OS thread doing the very same header load. Earlier, starting one
here too (guessing the same import list via `Driver.resolveHeaderImports`)
doubled the per-session dedicated-thread count and was implicated in an
intermittent `lean_finalize_task_manager` exit hang under suite A's load
(many servers spawned back-to-back, 2026-09-07) -- removed for that reason. -/
def startPrewarm : IO Unit := do
  if !(← prewarmEnabled) then
    return ()
  let explicit ← prewarmImportsEnv
  if !explicit.isEmpty then
    let openT ← Driver.Config.openTimeout
    Driver.startHeaderPrewarm explicit openT

def main (argv : List String) : IO Unit := do
  -- `lake env` bootstrap (see `LeanMcpEvolve.Reexec`): root = LEAN_PROJECT_ROOT,
  -- else the LEAN_TASK_FILE preset's nearest lakefile ancestor. Interactive
  -- use (no preset, no root) is unaffected.
  let root? ← match ← IO.getEnv "LEAN_PROJECT_ROOT" with
    | some r => if r ≠ "" then pure (some (System.FilePath.mk r)) else pure none
    | none => match ← IO.getEnv "LEAN_TASK_FILE" with
      | some f => if f ≠ "" then Reexec.findRoot ((System.FilePath.mk f).parent.getD ".") else pure none
      | none => pure none
  Reexec.reexecUnderLakeEnv root? argv
  let ref ← IO.mkRef (none : Option Driver.Session)
  -- Kick off the header-only prewarm FIRST (README "Excluding Mathlib import
  -- time from attempt budgets") -- `Session.startEagerOpen`'s own full open
  -- (below) will, via `Driver.openFile` → `Driver.acquireHeaderState`, wait
  -- on this same background task rather than redoing the import itself when
  -- their import lists match, so the two never pay `import Mathlib` twice.
  startPrewarm
  -- Kick off the `LEAN_TASK_FILE` preset's open in the background now (see
  -- `Session.startEagerOpen`) so its cost overlaps the MCP handshake
  -- instead of landing entirely inside the first tool call's wall budget.
  -- `LEAN_EAGER_OPEN=0` disables it; `Mcp.run` below never waits on it.
  Session.startEagerOpen ref
  let tools := Session.allTools ref
  let enabled ← do
    match ← IO.getEnv "LEAN_ENABLE_TOOLS" with
    | some raw =>
      let names := (raw.splitOn ",").filterMap fun x =>
        let t := Hints.trimStr x
        if t == "" then none else some t
      pure (if names.isEmpty then Session.defaultEnabled else names)
    | none => pure Session.defaultEnabled
  let selected := tools.filter (fun t => enabled.contains t.name)
  -- `onExit`: one `kind: shutdown` JSONL record reporting the process-wide
  -- total import wait (README's harness recipe sums it independently from
  -- the `import` records themselves, but this is a convenient single number).
  Mcp.run selected (onExit := do
    let ts ← Mcp.wallClockNow
    let total ← Mcp.getImportMsTotal
    Mcp.emitLog [("ts", toJson ts), ("kind", Json.str "shutdown"), ("import_ms_total", toJson total)])
