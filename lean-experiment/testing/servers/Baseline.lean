/-
`lean-mcp-baseline` — the deliberately-naive control server (testing/README.md
§"Servers"), a port of rocq-mcp-evolve's `src/baseline_server/rocq_agent_baseline.ml`.

One tool, `check`: the agent submits a COMPLETE `.lean` file; the server
compiles it from scratch with `lake env lean` (run inside `LEAN_PROJECT_ROOT`
so `import Mathlib` resolves) and returns the raw compiler exit code and
output verbatim. No sessions, no incremental checking, no state, no search —
every call pays full recompilation cost, exactly like a human running
`lake env lean` in a loop.

Reuses `LeanMcpEvolve.Mcp` (`Tool`, `textResult`, `run`, `emitLog` via the
tool-call dispatch already in `Mcp.handleToolsCall`), `LeanMcpEvolve.Proc`
(`Proc.run`, the timeout+kill subprocess runner) and
`LeanMcpEvolve.Session.workdir` (the `LEAN_WORKDIR` helper) rather than
hand-rolling any of the JSON-RPC loop or process plumbing.

Deviation from the OCaml original (documented in testing/README.md's
Deviations table too): the OCaml `check` ran `rocq compile proof.v` with
`cwd` = the workdir itself (Rocq has no project-root concept). Lean's
`import Mathlib` needs the Mathlib project's `LEAN_PATH`, which only
`lake env lean` run *inside* that project resolves, so here `cwd` is
`LEAN_PROJECT_ROOT` (falling back to the workdir if unset) and the compiled
file is referenced by its absolute path.
-/
import LeanMcpEvolve.Mcp
import LeanMcpEvolve.Proc
import LeanMcpEvolve.Session

open Lean (Json toJson)
open LeanMcpEvolve

/-- `%g`-free float parser for env vars of the form `"60"` / `"12.5"` — a
self-contained copy of `Driver.Config`'s private `parseFloat` (that one is
file-private, so it cannot be reused directly from here). -/
private def parseFloatEnv (s : String) : Option Float :=
  match s.trim.splitOn "." with
  | [whole] => whole.toNat?.map Float.ofNat
  | [whole, frac] =>
    match whole.toNat?, frac.toNat? with
    | some w, some f => some (Float.ofNat w + Float.ofNat f / (10.0 : Float) ^ (Float.ofNat frac.length))
    | _, _ => none
  | _ => none

/-- `ROCQ_COMPILE_TIMEOUT` analogue: seconds `lake env lean` may run before
being killed. Default 60, matching the OCaml original. -/
def compileTimeout : IO Float := do
  match ← IO.getEnv "LEAN_COMPILE_TIMEOUT" with
  | some s => pure ((parseFloatEnv s).getD 60.0)
  | none => pure 60.0

/-- `LEAN_PROJECT_ROOT`, if set and non-empty; else `dir` (the workdir),
mirroring the spec's fallback for where `lake env lean` is invoked. -/
def projectRootOr (dir : System.FilePath) : IO System.FilePath := do
  match ← IO.getEnv "LEAN_PROJECT_ROOT" with
  | some r => pure (if r ≠ "" then System.FilePath.mk r else dir)
  | none => pure dir

def checkTool : Mcp.Tool :=
  { name := "check"
    description :=
      "Compile a complete Lean 4 (.lean) file from scratch. Pass the ENTIRE \
       file contents: imports, the theorem statement exactly as given, and \
       your proof. Returns the compiler exit code and its full output. Exit \
       code 0 means the whole file was accepted."
    inputSchema := Json.mkObj
      [ ("type", "object")
      , ("properties", Json.mkObj
          [ ("content", Json.mkObj
              [ ("type", "string")
              , ("description", "Complete contents of the .lean file") ]) ])
      , ("required", Json.arr #["content"]) ]
    handler := fun args => do
      match args.getObjValD "content" with
      | .str content => do
        let dir ← Session.workdir
        let path := dir / "proof.lean"
        IO.FS.writeFile path content
        let cwd ← projectRootOr dir
        let timeoutS ← compileTimeout
        let r ← Proc.run "lake" #["env", "lean", path.toString] (cwd := some cwd) (timeoutS := timeoutS)
        -- harness contract: candidate.lean = latest content that fully checked
        if r.exitCode == 0 then
          IO.FS.writeFile (dir / "candidate.lean") content
        let suffix := if r.timedOut then " (compilation TIMED OUT and was killed)" else ""
        let body := s!"exit code: {r.exitCode}{suffix}\n{r.output}"
        pure (Mcp.textResult body (log :=
          [ ("prover_ms", toJson r.durMs.toFloat)
          , ("exit_code", toJson r.exitCode)
          , ("timed_out", toJson r.timedOut)
          , ("content_chars", toJson content.length) ]))
      | _ => pure (Mcp.textResult "missing required argument: content" (isError := true)) }

def main : IO Unit := Mcp.run [checkTool]
