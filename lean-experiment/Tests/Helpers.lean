/-
Tests.Helpers — mini-lib for the integration suites (mirrors
`prototype-python/tests/helpers.py`, see `prototype-python/tests/ARCHITECTURE.md`
"helpers.py contract"): spawn the real server binary over MCP stdio, send
JSON-RPC lines, assert on behaviour. No mocks, no framework beyond what this
file provides.
-/
import Lean
import LeanMcpEvolve.Text

namespace Tests.Helpers

open Lean (Json ToJson toJson)

-- --- small string helpers -------------------------------------------------

/-- Does `s` contain `needle` as a substring? -/
def contains (s needle : String) : Bool :=
  (s.splitOn needle).length > 1

/-- Does `s` start with `pre`? -/
def startsWith (s pre : String) : Bool :=
  s.startsWith pre

/-- A numeric field from a parsed JSONL record (e.g. `dur_ms`/`import_ms` in
`LEAN_LOG_FILE` instrumentation), as a `Float`. A huge sentinel (never under
any real threshold check) when the field is absent or not a number, so a
missing field fails an upper-bound assertion loudly instead of vacuously
passing on `0.0`. -/
def getFloatField (j : Json) (key : String) : Float :=
  match (j.getObjValD key).getNum? with
  | .ok n => n.toFloat
  | .error _ => 1e18

-- --- filesystem plumbing ---------------------------------------------------

/-- Walk up from `dir` until a `lakefile.toml` is found (the repo root). -/
partial def findRepoRoot (dir : System.FilePath) : IO System.FilePath := do
  if ← (dir / "lakefile.toml").pathExists then
    pure dir
  else
    match dir.parent with
    | some p => findRepoRoot p
    | none => throw (IO.userError "Tests.Helpers: could not find repo root (lakefile.toml) above cwd")

/-- The lean-mcp-evolve repo root, found by walking up from the current
working directory (so this works whether invoked as `lake exe tests` from
the repo root, which is the expected invocation). -/
def repoRoot : IO System.FilePath := do
  findRepoRoot (← IO.Process.getCurrentDir)

/-- Absolute path to the built server executable. -/
def serverBinPath : IO System.FilePath := do
  pure ((← repoRoot) / ".lake" / "build" / "bin" / "lean-mcp-evolve")

/-- `True` iff the server binary exists (used to decide whether suites A/M can
run yet, while the server implementation is produced concurrently). -/
def serverBinExists : IO Bool := do
  (← serverBinPath).pathExists

def fixture (name : String) : IO String := do
  IO.FS.readFile ((← repoRoot) / "Tests" / "Fixtures" / name)

/-- Write `content` to `path`, creating parent directories as needed (mirrors
Python's `write_file`, which does `os.makedirs(dirname, exist_ok=True)`). -/
def writeFile (path : System.FilePath) (content : String) : IO Unit := do
  match path.parent with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()
  IO.FS.writeFile path content

def readFile (path : System.FilePath) : IO String :=
  IO.FS.readFile path

/-- A fresh temp directory (not auto-deleted; matches Python's
`tempfile.mkdtemp`, which also leaves the directory around for post-mortem
inspection). The `prefix` argument is accepted for parity with the Python
helper's signature but not reflected in the generated name (this toolchain's
`IO.FS.createTempDir` takes no prefix). -/
def tmpdir (_prefix : String := "lean_mcp_test_") : IO System.FilePath :=
  IO.FS.createTempDir

-- --- unique fixture names ---------------------------------------------------

initialize taskCounterRef : IO.Ref Nat ← IO.mkRef 0

/-- A fresh, valid Lean-module-name-safe suffix ("1", "2", ...), used to name
fixture files written into the core project so concurrent/sequential test
cases never collide (Python relies on `tempfile.mkdtemp`'s random suffix for
this; we use a counter instead since it is guaranteed identifier-safe). -/
def freshSuffix : IO Nat :=
  taskCounterRef.modifyGet (fun n => (n + 1, n + 1))

-- --- core (dependency-free) test project ------------------------------------

initialize coreProjectRef : IO.Ref (Option System.FilePath) ← IO.mkRef none

/-- The content of our own `lean-toolchain` file (the core project must use
the very toolchain this server was built with — the server can only load
`.olean`s built by the same Lean version, see docs/PLAN.md §1). -/
def ownToolchain : IO String := do
  IO.FS.readFile ((← repoRoot) / "lean-toolchain")

def buildCoreProject : IO System.FilePath := do
  let d ← IO.FS.createTempDir
  IO.FS.writeFile (d / "lakefile.toml")
    "name = \"coreproj\"\nversion = \"0.1.0\"\ndefaultTargets = [\"Coreproj\"]\n\n[[lean_lib]]\nname = \"Coreproj\"\n"
  let tc ← ownToolchain
  IO.FS.writeFile (d / "lean-toolchain") tc
  IO.FS.createDirAll (d / "Coreproj")
  IO.FS.writeFile (d / "Coreproj" / "Basic.lean") "theorem helper (n : Nat) : n + 0 = n := by simp\n"
  IO.FS.writeFile (d / "Coreproj.lean") "import Coreproj.Basic\n"
  let out ← IO.Process.output { cmd := "lake", args := #["build"], cwd := some d }
  if out.exitCode != 0 then
    throw (IO.userError s!"lake build of the core test project failed:\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}")
  pure d

/-- A dependency-free Lake project, built once per test-executable run, that
fixtures for suite A are written into (so the server's own project-load-path
discovery, `lake env printenv LEAN_PATH`, resolves them). -/
def coreProject : IO System.FilePath := do
  match ← coreProjectRef.get with
  | some d => pure d
  | none =>
    let d ← buildCoreProject
    coreProjectRef.set (some d)
    pure d

-- --- Mathlib-backed project (suite M), optional -----------------------------

/-- `some <project>` iff `LEAN_MCP_TEST_MATHLIB_PROJECT` is set and points at
a project with a built Mathlib dependency; `none` (⇒ skip suite M)
otherwise. -/
def mathlibProject : IO (Option System.FilePath) := do
  match ← IO.getEnv "LEAN_MCP_TEST_MATHLIB_PROJECT" with
  | none => pure none
  | some p =>
    if p.isEmpty then
      pure none
    else
      let fp : System.FilePath := p
      if ← (fp / ".lake" / "packages" / "mathlib").pathExists then
        pure (some fp)
      else
        pure none

-- --- the server under test --------------------------------------------------

/-- Stdio configuration for the spawned server: everything piped (stderr is
drained in the background and otherwise ignored, matching the "piped and
ignored" option from the plan — a `null` stderr would risk the child
blocking on a full pipe if `LEAN_MCP_DEBUG` tracing is ever turned on). -/
def stdioCfg : IO.Process.StdioConfig :=
  { stdin := .piped, stdout := .piped, stderr := .piped }

/-- The `StdioConfig` a `Child` has after `takeStdin` closes its stdin. -/
def closedStdinCfg : IO.Process.StdioConfig :=
  { stdioCfg with stdin := .null }

/-- A running server process, talking newline-delimited JSON-RPC 2.0 over
stdio (MCP transport, see `LeanMcpEvolve.Mcp`). -/
structure Server where
  child  : IO.Process.Child stdioCfg
  idRef  : IO.Ref Nat

/-- Spawn the built `lean-mcp-evolve` binary via `lake env` (so `LEAN_PATH`
resolves the project's dependencies — Mathlib, or the core project itself),
in the given project directory, with `envAdds` layered onto the inherited
environment. -/
def spawnServer (cwd : System.FilePath) (envAdds : List (String × String)) : IO Server := do
  let bin ← serverBinPath
  let child ← IO.Process.spawn
    { cmd := "lake"
      args := #["env", bin.toString]
      cwd := some cwd
      env := (envAdds.map fun (k, v) => (k, some v)).toArray
      stdin := .piped, stdout := .piped, stderr := .piped }
  -- drain stderr in the background so a chatty child (LEAN_MCP_DEBUG=1)
  -- never blocks on a full pipe.
  let _ ← IO.asTask (discard child.stderr.readToEnd) Task.Priority.dedicated
  let idRef ← IO.mkRef 0
  pure { child, idRef }

/-- Read stdout lines until the one whose `"id"` matches `id` (unparsable or
mismatched lines are skipped — the same lenient loop as the Python helper's
`rpc`). Blocks; per the plan we rely on the server's own tool timeouts rather
than a client-side deadline. -/
partial def readResponse (h : IO.FS.Handle) (id : Nat) : IO Json := do
  let line ← h.getLine
  if line.isEmpty then
    throw (IO.userError s!"server closed stdout while waiting for a response (id={id})")
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then
    readResponse h id
  else
    match Json.parse trimmed with
    | .error _ => readResponse h id
    | .ok j =>
      match (j.getObjValD "id").getNat? with
      | .ok n => if n == id then pure j else readResponse h id
      | .error _ => readResponse h id

/-- Send one JSON-RPC request and block for the matching response. -/
def Server.rpc (s : Server) (method : String) (params : Json := Json.mkObj []) : IO Json := do
  let id ← s.idRef.modifyGet (fun n => (n + 1, n + 1))
  let msg := Json.mkObj
    [("jsonrpc", "2.0"), ("id", toJson id), ("method", method), ("params", params)]
  s.child.stdin.putStr (msg.compress ++ "\n")
  s.child.stdin.flush
  readResponse s.child.stdout id

def Server.initialize (s : Server) : IO Json :=
  s.rpc "initialize" (Json.mkObj [("protocolVersion", "2024-11-05"), ("clientInfo", Json.mkObj [("name", "test")])])

def Server.tools (s : Server) : IO (List String) := do
  let r ← s.rpc "tools/list"
  match ((r.getObjValD "result").getObjValD "tools").getArr? with
  | .error _ => pure []
  | .ok arr =>
    pure (arr.toList.map fun t => match t.getObjValD "name" with
      | .str n => n
      | _ => "")

/-- Call a tool; returns the concatenated `text` of every content block, or
`"RPC ERROR: ..."` if the JSON-RPC response itself carried an `"error"`
(protocol-level error, e.g. an unknown tool name). -/
def Server.call (s : Server) (name : String) (args : Json := Json.mkObj []) : IO String := do
  let r ← s.rpc "tools/call" (Json.mkObj [("name", name), ("arguments", args)])
  match r.getObjVal? "error" with
  | .ok errJ => pure ("RPC ERROR: " ++ errJ.compress)
  | .error _ =>
    match ((r.getObjValD "result").getObjValD "content").getArr? with
    | .error _ => pure ""
    | .ok arr =>
      pure (String.intercalate "\n" (arr.toList.map fun c => match c.getObjValD "text" with
        | .str t => t
        | _ => ""))

partial def waitOrKill (child : IO.Process.Child closedStdinCfg) (triesLeft : Nat) : IO Unit := do
  match ← child.tryWait with
  | some _ => pure ()
  | none =>
    if triesLeft == 0 then
      child.kill
    else
      IO.sleep 100
      waitOrKill child (triesLeft - 1)

/-- Close stdin (giving the child an EOF marker), wait briefly, then kill if
it hasn't exited (mirrors the Python helper's `close`, which does the same
followed by a process-group kill on timeout). -/
def Server.close (s : Server) : IO Unit := do
  try
    let (_, child2) ← s.child.takeStdin
    waitOrKill child2 50
  catch _ => pure ()

-- --- TAP-ish reporting -------------------------------------------------------

structure Stats where
  passed : Nat := 0
  failed : Nat := 0
  failures : List String := []

/-- Record and print one assertion. `actual`, when given, is printed
(truncated to 600 chars) alongside a failure, to make routing the bug back to
the planner possible without re-running anything. -/
def check (statsRef : IO.Ref Stats) (cond : Bool) (name : String) (actual : String := "") : IO Unit := do
  if cond then
    statsRef.modify (fun s => { s with passed := s.passed + 1 })
    IO.println s!"ok - {name}"
  else
    statsRef.modify (fun s => { s with failed := s.failed + 1, failures := s.failures ++ [name] })
    IO.println s!"FAIL - {name}"
    if !actual.isEmpty then
      let chars := actual.toList
      let truncated := if chars.length > 600 then String.mk (chars.take 600) ++ " …[truncated]" else actual
      IO.println truncated

end Tests.Helpers
