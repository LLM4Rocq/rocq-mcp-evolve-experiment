/-
`LeanMcpEvolve.Reexec` — the `lake env` bootstrap shared by the server and
the gate executables.

Both binaries need the target project's toolchain environment: `LEAN_PATH`
(so `import Mathlib` resolves) and `LEAN_SYSROOT` (so `Init` comes from the
project's Lean, not from whatever `lean --print-prefix` resolves to from the
process's cwd — elan picks the *default* toolchain outside a project tree).
Setting the search path programmatically is not enough: the REPL's
`processInput` and the header processing in `Text.findDecls` re-derive the
search path from the environment, so a process launched without those
variables elaborated Mathlib files against a core-only (or version-mismatched)
environment and reported spurious parse errors ("pattern-matching decl",
"expected token") — observed 2026-09-06 on the PutnamBench harness, which
starts the binaries directly rather than via `lake env`.

Fix: when `LEAN_PATH` is unset and a project root is known, ask `lake env
printenv` in that root for `LEAN_PATH`, `LEAN_SYSROOT` and `PATH`, and re-exec
this very binary with them exported -- same cwd and argv (a `lake env <self>`
wrapper would change the cwd to the root and break relative paths in argv),
forwarding stdio and the exit code. `LEAN_NO_REEXEC=1` disables the bootstrap (and is set on the
child to rule out loops).
-/

namespace LeanMcpEvolve.Reexec

def hasLakefile (dir : System.FilePath) : IO Bool := do
  return (← (dir / "lakefile.lean").pathExists) || (← (dir / "lakefile.toml").pathExists)

/-- Nearest ancestor of `p` (inclusive) with a lakefile, if any. -/
partial def findRoot (p : System.FilePath) (fuel : Nat := 200) : IO (Option System.FilePath) := do
  if fuel == 0 then return none
  if ← hasLakefile p then return some p
  match p.parent with
  | some q => if q == p then return none else findRoot q (fuel - 1)
  | none => return none

/-- `lake env printenv <name>` in `root`, or `none` if lake fails / prints nothing. -/
def lakePrintenv (root : System.FilePath) (name : String) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := "lake", args := #["env", "printenv", name], cwd := some root }
    let v := out.stdout.trimAscii.copy
    return if out.exitCode == 0 && !v.isEmpty then some v else none
  catch _ => return none

/-- Re-exec this binary with the project's toolchain environment exported if
`LEAN_PATH` is unset; never returns in that case (exits with the child's code).
The child keeps the caller's cwd and argv verbatim (so relative paths in argv
still resolve) -- only `LEAN_PATH`, `LEAN_SYSROOT` and `PATH` (toolchain `bin`
first) are taken from `lake env` in `root`. Returns `()` when no re-exec is
needed or possible (no root, no lakefile, `LEAN_NO_REEXEC` set, `lake` missing). -/
def reexecUnderLakeEnv (root? : Option System.FilePath) (argv : List String) : IO Unit := do
  if (← IO.getEnv "LEAN_PATH").isSome then return ()
  if (← IO.getEnv "LEAN_NO_REEXEC").isSome then return ()
  let some root := root? | return ()
  if !(← hasLakefile root) then return ()
  let some leanPath ← lakePrintenv root "LEAN_PATH" | return ()
  let sysroot? ← lakePrintenv root "LEAN_SYSROOT"
  let path? ← lakePrintenv root "PATH"
  let self ← IO.appPath
  let env : Array (String × Option String) :=
    #[("LEAN_PATH", some leanPath), ("LEAN_NO_REEXEC", some "1")]
      ++ (match sysroot? with | some s => #[("LEAN_SYSROOT", some s)] | none => #[])
      ++ (match path? with | some p => #[("PATH", some p)] | none => #[])
  let child ← try
      IO.Process.spawn {
        cmd := self.toString, args := argv.toArray, env := env,
        stdin := .inherit, stdout := .inherit, stderr := .inherit }
    catch _ => return ()
  let code ← child.wait
  IO.Process.exit code.toUInt8

end LeanMcpEvolve.Reexec
