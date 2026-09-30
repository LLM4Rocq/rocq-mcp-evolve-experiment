# Phase 1 notes: REPL API on `v4.27.0-rc1`

## APIs that worked, exactly
- `Lean.Elab.IO.processInput (input) (cmdState? : Option Command.State)
  (opts := {}) (fileName := none) : IO (Command.State × Command.State ×
  List Message × List InfoTree)` (`REPL/Frontend.lean`) — call twice:
  prefix with `cmdState? := none`, then `theorem <name> ... := by sorry`
  with `cmdState? := some <prefix's 2nd component>`. Body is `unsafe do`
  but the signature is plain `IO`, callable from an ordinary `main`.
- `Lean.Elab.InfoTree.sorries : InfoTree → List (ContextInfo × SorryType ×
  Position × Position)` + `REPL.ProofSnapshot.create ctx lctx? env? goals
  rootGoals?` — for `.tactic g`, get the mvar's `LocalContext` via
  `ctx.runMetaM {} (ctx.mctx.findDecl? g)`. `env?` must be the environment
  *before* the sorry-introducing command (`cmdStateBefore.env`), matching
  `REPL.Main.runCommand`'s `sorries trees initialCmdState.env none`.
- `ProofSnapshot.ppGoals` / `.runString` as documented; `REPL.
  getProofStatus`'s body never touches REPL's own `State` monad, so it
  ports verbatim to plain `IO String`. Confirmed "Completed" on a real
  `nlinarith` close.
- `REPL.Main` is **not imported**: `main`/`repl`/`parse`/`Input` live in its
  root namespace (its own `lean_exe` uses `root := REPL.Main`), colliding
  with `Probe.lean`'s `main`. We copy, with attribution, the 2 functions
  needed: `getProofStatus` and the sorry→`ProofSnapshot` half of
  `REPL.sorries`.

## Timeout / cancellation — what actually worked
Run the tactic via `IO.asTask`; poll `IO.hasFinished` every 50ms against a
wall-clock deadline (`IO.monoMsNow`), never blocking on `task.get`; on
timeout, call `tk.set` on an `IO.CancelToken` in `Core.Context.cancelTk?`
(best effort), then **stop waiting and return**.
- `Core.checkInterrupted` is purely cooperative (checked only between
  elaboration steps) — cannot interrupt one opaque kernel reduction (e.g.
  `decide`), which never yields.
- `Core.Context.maxHeartbeats` also raised to 1e8 before running, isolating
  the wall-clock mechanism from heartbeats (`CoreM.toIO` resets
  `initHeartbeats` fresh per nested run, so it's a per-call budget).
- What actually keeps the process responsive: nothing stops the runaway
  `decide` itself (worker thread keeps running) — `main` abandons the wait
  and returns; OS process exit takes the worker thread with it. Verified:
  `decide` budget 3 printed `TIMEOUT`, process (`ps aux`) fully gone within
  ~1s of the deadline.
- Implication for `Driver.lean` (2b): cancel-token/heartbeat-cap are
  best-effort only — a long-lived server can't rely on its own exit to
  reclaim a leaked thread; flagged for the Driver design.

## Measured timings (`lake env` in `/Users/jviennot/Documents/Cours/LEAN_2026`)
First run after `lake build` (cold page cache, `import Mathlib` +
`nlinarith` closing the goal): **44.1s** wall. Warm-cache runs: `nra`
(parse error) 6.3s; `linarith` (tactic failure) 5.8s; `decide`, 3s budget →
`TIMEOUT` at 9.3s total (~6s overhead + budget), clean exit.

## Pitfalls
- `String.trim`/`.drop` now return `String.Slice`, not `String` — call
  `.toString`, or use `.trimAscii` (REPL itself works around this with
  `trimAscii`/`trimAsciiEnd`).
- `ProofSnapshot.create`'s `lctx?`/`rootGoals?` are `Option`-typed but call
  sites (ours and REPL's) pass bare values — works via stdlib's generic
  `instance : Coe α (Option α)`. `supportInterpreter = true` set on both
  `lean_exe`s per the plan, unused so far; `processInput` already calls
  `enableInitializersExecution`, so `Probe.lean` needn't.
