/-
LeanMcpEvolve.GateMain — the `gate` executable's entry point (docs/PLAN.md's
correctness GATE, see `LeanMcpEvolve.Gate`'s module doc). Deliberately its
own `lean_exe` (`root = "LeanMcpEvolve.GateMain"`, not folded into
`LeanMcpEvolve.Main`): the whole point of the gate is that it runs in its
OWN process, separate from the server/session process whose tactics it is
meant to distrust.

Usage: `gate <candidate.lean> --theorem <name> [--reference <reference.lean>]
[--project <root>] [--json]`.
-/
import LeanMcpEvolve.Gate
import LeanMcpEvolve.Reexec

open LeanMcpEvolve

def usage : String :=
  "usage: gate <candidate.lean> --theorem <name> [--reference <reference.lean>] [--project <root>] [--json]"

structure Args where
  candidate  : Option System.FilePath := none
  theoremName : Option String := none
  reference  : Option System.FilePath := none
  project    : Option System.FilePath := none
  json       : Bool := false

private partial def parseArgs (args : List String) (acc : Args) : Except String Args :=
  match args with
  | [] => .ok acc
  | "--theorem" :: v :: rest => parseArgs rest { acc with theoremName := some v }
  | "--reference" :: v :: rest => parseArgs rest { acc with reference := some (System.FilePath.mk v) }
  | "--project" :: v :: rest => parseArgs rest { acc with project := some (System.FilePath.mk v) }
  | "--json" :: rest => parseArgs rest { acc with json := true }
  | ["--theorem"] => .error "--theorem requires a value"
  | ["--reference"] => .error "--reference requires a value"
  | ["--project"] => .error "--project requires a value"
  | v :: rest =>
    if acc.candidate.isNone then parseArgs rest { acc with candidate := some (System.FilePath.mk v) }
    else .error s!"unexpected argument: {v}"

private def verdictJson (theoremName : String) (v : Gate.Verdict) : Lean.Json :=
  Lean.Json.mkObj [
    ("accepted", Lean.toJson v.accepted),
    ("reason", Lean.toJson v.reason),
    ("target", Lean.toJson theoremName),
    ("axioms", Lean.toJson (v.axioms.map toString)),
    ("unreplayed", Lean.toJson (v.unreplayed.map toString))]

def main (argv : List String) : IO Unit := do
  -- `lake env` bootstrap (see `LeanMcpEvolve.Reexec`): root = --project, else
  -- the candidate's nearest lakefile ancestor.
  (match parseArgs argv {} with
   | .ok args => do
     let root? ← match args.project with
       | some p => pure (some p)
       | none => match args.candidate with
         | some c => Reexec.findRoot (c.parent.getD ".")
         | none => pure none
     Reexec.reexecUnderLakeEnv root? argv
   | .error _ => pure ())
  match parseArgs argv {} with
  | .error e =>
    IO.eprintln s!"error: {e}"
    IO.eprintln usage
    IO.Process.exit 2
  | .ok args =>
    match args.candidate, args.theoremName with
    | none, _ =>
      IO.eprintln "error: missing <candidate.lean>"
      IO.eprintln usage
      IO.Process.exit 2
    | _, none =>
      IO.eprintln "error: missing --theorem <name>"
      IO.eprintln usage
      IO.Process.exit 2
    | some candidate, some theoremName =>
      let verdict ← Gate.run candidate theoremName args.reference args.project
      if args.json then
        IO.println (verdictJson theoremName verdict).compress
      else if verdict.accepted then
        IO.println "ACCEPTED"
      else
        IO.println s!"REJECTED: {verdict.reason}"
      IO.Process.exit (if verdict.accepted then 0 else 1)
