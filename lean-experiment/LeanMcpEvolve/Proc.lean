/-
Subprocess execution with a hard timeout and combined-output capture (the
`lake build` runs behind `verify` use this). Ported from
`prototype-python/src/lean_mcp_evolve/proc.py`, adapted to the process API
available on this toolchain (`IO.Process`).

Differences from the Python original, and why:
* `subprocess.STDOUT` (redirect the child's stderr into the same pipe as
  stdout, giving a byte-accurate interleaving) has no equivalent in
  `IO.Process.Stdio`: a child's stdout/stderr can each only be `piped`,
  `inherit`, or `null`. We pipe both separately and read them concurrently
  with `IO.asTask`, then concatenate `stdout ++ stderr` once both drain to
  EOF. This loses byte-level interleaving between the two streams (a line
  written to stderr right after one on stdout is not guaranteed to appear
  in the same relative order in `output`), but every line from both streams
  is preserved.
* Tree-kill: `IO.Process.SpawnArgs.setsid` starts the child in its own
  session/process group (POSIX `setsid`), and `IO.Process.Child.kill`'s
  documentation states that when the child was spawned with `setsid`, kill
  "terminates the entire process group instead" — i.e. this already gives
  us the whole-tree kill that the Python original gets from
  `os.killpg(os.getpgid(p.pid), SIGKILL)`.
* Waiting with a deadline: there is no `Popen.communicate(timeout=...)`
  equivalent, so we poll `Child.tryWait` against a wall-clock deadline
  (`IO.monoMsNow`), sleeping 50ms between polls, exactly as `Driver.lean`'s
  tactic-timeout mechanism does (see `docs/PHASE1_NOTES.md`).
-/

namespace LeanMcpEvolve.Proc

/-- Maximum number of UTF-8 bytes of `output` returned before truncation. -/
def maxOutputBytes : Nat := 200000

/-- The result of running a process to (attempted) completion. -/
structure Result where
  /-- The process's exit code, or `-1` if it had to be killed after timing out. -/
  exitCode : Int
  /-- Whether the process was killed because it exceeded `timeoutS`. -/
  timedOut : Bool
  /-- Combined stdout+stderr, capped at `maxOutputBytes` UTF-8 bytes. -/
  output : String
  /-- Wall-clock duration of the call, in milliseconds. -/
  durMs : Nat
  deriving Repr

/-- Shrinks `n` (a candidate byte-length prefix of `bytes`) down until
`bytes.extract 0 n` is valid UTF-8. UTF-8 continuation bytes make this take
at most 3 steps starting from any `n`. -/
partial def shrinkToValidUtf8 (bytes : ByteArray) (n : Nat) : Nat :=
  if n == 0 then
    0
  else
    match String.fromUTF8? (bytes.extract 0 n) with
    | some _ => n
    | none => shrinkToValidUtf8 bytes (n - 1)

/-- Caps `s` at `maxOutputBytes` UTF-8 bytes, appending a truncation notice
(matching the prototype's wording) when it does. -/
def capOutput (s : String) : String :=
  let bytes := s.toUTF8
  let total := bytes.size
  if total <= maxOutputBytes then
    s
  else
    let n := shrinkToValidUtf8 bytes maxOutputBytes
    let head := (String.fromUTF8? (bytes.extract 0 n)).getD ""
    head ++ s!"\n[... output truncated: {maxOutputBytes} of {total} bytes shown]"

/-- Polls `child.tryWait` until it exits or `deadlineMs` (a `IO.monoMsNow`
timestamp) passes, sleeping 50ms between polls. -/
partial def waitForExit {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg)
    (deadlineMs : Nat) : IO (Option UInt32) := do
  match ← child.tryWait with
  | some code => pure (some code)
  | none =>
    let now ← IO.monoMsNow
    if now >= deadlineMs then
      pure none
    else do
      IO.sleep 50
      waitForExit child deadlineMs

/-- Waits for a background read task to finish, up to `deadlineMs`; gives up
(returning whatever has been read so far, i.e. `""` here since the task
result is atomic) if the deadline passes first. -/
partial def waitTaskDeadline (t : Task (Except IO.Error String)) (deadlineMs : Nat) : IO String := do
  if ← IO.hasFinished t then
    match ← IO.wait t with
    | .ok s => pure s
    | .error _ => pure ""
  else
    let now ← IO.monoMsNow
    if now >= deadlineMs then
      pure ""
    else do
      IO.sleep 50
      waitTaskDeadline t deadlineMs

/-- Runs `cmd args` to completion (or until `timeoutS` elapses, at which
point it is killed), capturing stdout and stderr concatenated together.
A missing executable is reported as `exitCode := 127` rather than thrown. -/
def run (cmd : String) (args : Array String) (cwd : Option System.FilePath := none)
    (timeoutS : Float := 60) (env : Array (String × Option String) := #[]) : IO Result := do
  let t0 ← IO.monoMsNow
  let spawnArgs : IO.Process.SpawnArgs := {
    cmd := cmd
    args := args
    cwd := cwd
    env := env
    setsid := true
    stdin := IO.Process.Stdio.null
    stdout := IO.Process.Stdio.piped
    stderr := IO.Process.Stdio.piped
  }
  let spawned ← try
      let child ← IO.Process.spawn spawnArgs
      pure (Except.ok child)
    catch e =>
      pure (Except.error e)
  match spawned with
  | .error e =>
    let t1 ← IO.monoMsNow
    pure { exitCode := 127, timedOut := false, output := s!"exec failed: {e}", durMs := t1 - t0 }
  | .ok child => do
    let stdoutTask ← IO.asTask child.stdout.readToEnd
    let stderrTask ← IO.asTask child.stderr.readToEnd
    let timeoutS := if timeoutS < 0 then 0 else timeoutS
    let timeoutMs := (timeoutS * 1000).toUInt64.toNat
    let deadlineMs := t0 + timeoutMs
    let exitCode? ← waitForExit child deadlineMs
    let timedOut := exitCode?.isNone
    if timedOut then
      child.kill
      -- Best-effort reap after the kill signal, matching the Python
      -- original's `communicate(timeout=5)` grace period.
      let _ ← waitForExit child ((← IO.monoMsNow) + 5000)
      pure ()
    let readDeadline := (← IO.monoMsNow) + 5000
    let outText ← waitTaskDeadline stdoutTask readDeadline
    let errText ← waitTaskDeadline stderrTask readDeadline
    let combined := outText ++ errText
    let capped := capOutput combined
    let t1 ← IO.monoMsNow
    -- On this runtime, a missing executable does not make `IO.Process.spawn`
    -- throw: the child is "spawned" but immediately exits after printing
    -- `could not execute external process '<cmd>'` to its output. Recognize
    -- that shape and report it the same way a `FileNotFoundError` would be
    -- reported in the Python original (`exitCode := 127`, error text kept).
    let execFailed := combined.startsWith "could not execute external process"
    let exitCode : Int :=
      if timedOut then -1
      else if execFailed then 127
      else Int.ofNat (exitCode?.getD 0).toNat
    pure { exitCode, timedOut, output := capped, durMs := t1 - t0 }

end LeanMcpEvolve.Proc
