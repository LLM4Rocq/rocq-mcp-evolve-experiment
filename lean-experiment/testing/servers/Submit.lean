/-
`lean-mcp-submit` — sidecar for external-tool configs (testing/README.md
§"Servers"), a port of rocq-mcp-evolve's `src/submit_server/rocq_agent_submit.ml`.
The ONLY thing it does is receive the agent's final complete `.lean` file and
write it to `$LEAN_WORKDIR/candidate.lean` so the standard correctness gate
(`LeanMcpEvolve.Gate`, run out-of-process) can verify it from scratch. No
compilation, no trust — a wrong submission simply fails the gate.

Reuses `LeanMcpEvolve.Mcp` (`Tool`, `textResult`, `run`) and
`LeanMcpEvolve.Session.workdir` (the `LEAN_WORKDIR` helper); no
`LeanMcpEvolve.Proc` needed since this tool never spawns a subprocess.
-/
import LeanMcpEvolve.Mcp
import LeanMcpEvolve.Session

open Lean (Json toJson)
open LeanMcpEvolve

/-- `Printf.sprintf "%03d"` — zero-pads `n`'s decimal representation to at
least 3 digits (wider once `n ≥ 1000`, matching `%03d`'s own behaviour). -/
private def pad3 (n : Nat) : String :=
  let s := toString n
  String.mk (List.replicate (3 - s.length) '0') ++ s

def submitTool : Mcp.Tool :=
  { name := "submit"
    description :=
      "Submit your FINAL complete .lean file (imports + statement exactly as \
       given + your proof). Call this exactly once, when you believe the \
       proof is finished — an external checker verifies it from scratch; \
       submissions that don't compile or violate the rules are rejected. \
       This is the only way your proof gets counted."
    inputSchema := Json.mkObj
      [ ("type", "object")
      , ("properties", Json.mkObj
          [ ("content", Json.mkObj
              [ ("type", "string")
              , ("description", "Complete contents of the final .lean file") ]) ])
      , ("required", Json.arr #["content"]) ]
    handler := fun args => do
      match args.getObjValD "content" with
      | .str content => do
        -- A76 parity (see the OCaml original): keep every submission
        -- versioned, so a later broken submit can never clobber an earlier
        -- good one; grading takes the newest submission that compiles.
        let dir ← Session.workdir
        let subs := dir / "submissions"
        IO.FS.createDirAll subs
        let n := (← (try subs.readDir catch _ => pure #[])).size
        let name := s!"{pad3 n}.lean"
        IO.FS.writeFile (subs / name) content
        IO.FS.writeFile (dir / "candidate.lean") content
        pure (Mcp.textResult
          "Submitted. If it passes external verification it counts as solved. Reply DONE."
          (log := [ ("content_chars", toJson content.length) ]))
      | _ => pure (Mcp.textResult "missing required argument: content" (isError := true)) }

def main : IO Unit := Mcp.run [submitTool]
