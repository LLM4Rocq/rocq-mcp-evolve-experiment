/-
Tests.Main — the `tests` executable (docs/PLAN.md phase 4): runs suites T
(pure `LeanMcpEvolve.Text` unit checks), A (session-server core contracts,
spawning the real server binary against a core-only project) and M
(Mathlib-backed contracts, skipped without `LEAN_MCP_TEST_MATHLIB_PROJECT`).

Usage: `lake exe tests [T|A|M]` — an optional argument selects a single
suite; with none, all three run in order. Prints a TAP-ish `ok - <name>` /
`FAIL - <name>` line per assertion, then a `N passed, M failed` summary, and
exits 1 iff any assertion failed.
-/
import Tests.Helpers
import Tests.Text
import Tests.Session
import Tests.Gate
import Tests.Mathlib

open Tests.Helpers (Stats)

def main (args : List String) : IO Unit := do
  let statsRef ← IO.mkRef ({} : Stats)
  let which := args.headD ""
  let runAll := which.isEmpty
  if runAll || which == "T" then
    IO.println "# suite T (LeanMcpEvolve.Text)"
    Tests.Text.run statsRef
  if runAll || which == "A" then
    IO.println "# suite A (session core, core-only project)"
    Tests.Session.run statsRef
  if runAll || which == "D" then
    IO.println "# suite D (Gate)"
    Tests.Gate.run statsRef
  if runAll || which == "M" then
    IO.println "# suite M (Mathlib-backed)"
    Tests.Mathlib.run statsRef
  let stats ← statsRef.get
  IO.println s!"{stats.passed} passed, {stats.failed} failed"
  if stats.failed > 0 then
    IO.Process.exit 1
