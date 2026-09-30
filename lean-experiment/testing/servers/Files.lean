/-
`lean-mcp-files` — the file-workspace MCP sidecar for the phase-2
autoformalization-tool-surface arm (AF_TOOLS_SPEC.md §1), a port of
rocq-mcp-evolve's `src/files_server/rocq_agent_files.ml`. ALL experiment arms
in that family get exactly these five tools, so the measured delta between
arms is the attached prover-server tools alone. Evaluation scaffolding — not
shipped as a product library.

Workspace root: `$LEAN_WORKSPACE` (all paths are relative to it; absolute
paths and `..` segments are rejected). Every response string, tool name,
description and inputSchema is reproduced from the OCaml original with only
the substitutions AF_TOOLS_SPEC.md §1 calls for:
* `.v` → `.lean`, `dune build` → `lake build`, tool `dune_build` → `lake_build`.
* the `theories/Spec.v` example path in `write_file`'s description →
  `Putnam/Helper.lean` (the dataset layout §2 sets up).
* the forbidden-token list is the harness gate's own (`sorry`, `admit`,
  `axiom`, `native_decide`, `set_option`, `run_tac`, `run_cmd`, `#eval`,
  `#exit`, `unsafe`, `implemented_by`, `extern`, `ofReduceBool`,
  `ofReduceNat`, `sorryAx`, `addDecl`, `addDeclWithoutChecking`, `+native` —
  NOT `import`, since new files legitimately need imports), not the OCaml
  original's Rocq-specific six (`admit`/`Admitted`/`Axiom`/`Parameter`/
  `Hypothesis`/`Variable`).
* `ROCQ_WORKSPACE` → `LEAN_WORKSPACE` in the "not set" guard message.

Reuses `LeanMcpEvolve.Mcp` (`Tool`, `textResult`, `run` — the tool-call
dispatch there already handles `Mcp.emitLog` JSONL instrumentation for every
call, so no sidecar-specific logging plumbing is needed here beyond the
optional extra `log` fields `lake_build` asks for), `LeanMcpEvolve.Proc`
(`Proc.run`, the timeout+kill subprocess runner) and
`LeanMcpEvolve.Text.stripComments` (comment/string-aware blanking, already
written for Lean's `--`/`/- -/` syntax — reused as-is rather than
re-implementing a Rocq-flavoured `(* *)` stripper). Deliberately does NOT
import `LeanMcpEvolve.Session`/`Driver`/`Reexec`: this server never opens a
proof session and must not re-exec — it only shells out to `lake`, same as
`Baseline.lean`.

Deliberate deviations from the OCaml original, each noted where it matters
below:
* Locking (`lake_build`/`verify`'s shared build lock): the OCaml original
  uses `Unix.lockf`, a kernel-managed advisory lock that self-releases if
  the holder dies. Nothing on this toolchain's `IO.Process`/`IO.FS` surface
  exposes `flock`/`lockf`, so this uses the same atomic create-rename spin
  with a staleness timeout that `LeanMcpEvolve.Verify.lakeBuild` already
  uses for its own (unrelated) build lock — a *file*-based lock needs that
  staleness clock precisely because it has no such self-release property.
* `read_file` reads via `IO.FS.readFile`, which requires valid UTF-8 (the
  OCaml original reads raw bytes via `open_in_bin`); fine for `.lean`
  sources, which are always UTF-8.
* `verify`'s forbidden-token issue lines name the file by its path relative
  to the workspace root (e.g. `Putnam/putnam_1977_a3.lean`), not by
  `Filename.basename` as the OCaml original does — the fuller path is more
  useful once files can live in subdirectories (as the `Putnam/` dataset
  layout does), and matches what AF_TOOLS_SPEC.md's smoke test expects.
* Forbidden-token matching: identifier-shaped tokens (`sorry`, `admit`, …)
  are matched at word boundaries, like the OCaml original's `\b...\b`
  regexes; the three non-identifier tokens added for Lean (`#eval`, `#exit`,
  `+native`) are matched as plain substrings instead (they have no
  identifier boundary to speak of). Matching runs against
  `Text.stripComments`'s output, which — like the OCaml original's
  `strip_comments` — blanks comments but leaves string-literal *contents*
  untouched, so (as in the original) a token spelled inside a string
  literal still counts as a hit; this is not fixed here, to stay faithful.
* `lake_build`'s response omits the OCaml original's local 6000-character
  truncation (`AF_TOOLS_SPEC.md`'s explicit instruction: "full output
  returned (cap as Proc does)") — output is capped only by
  `Proc.capOutput`'s general 200000-byte cap, and its first line reads
  `exit code: N` (matching `Baseline.lean`'s house style) rather than the
  original's `exit N`.
-/
import LeanMcpEvolve.Mcp
import LeanMcpEvolve.Proc
import LeanMcpEvolve.Text

open Lean (Json toJson)
open LeanMcpEvolve

/-! ### workspace root -/

/-- `LEAN_WORKSPACE`, if set and non-empty. -/
def workspaceRoot? : IO (Option System.FilePath) := do
  match ← IO.getEnv "LEAN_WORKSPACE" with
  | some d => pure (if d ≠ "" then some (System.FilePath.mk d) else none)
  | none => pure none

/-- Port of the OCaml original's `failwith "ROCQ_WORKSPACE not set"`, but
returned as a normal `isError` tool result (not an uncaught exception) so
its wording reaches the agent verbatim instead of being wrapped as
`Mcp.handleToolsCall`'s generic "internal tool error: ...". -/
def workspaceNotSetMsg : String := "LEAN_WORKSPACE not set"

/-- `resolve`: a relative path (no leading `/`, no `..` segment) joined onto
the workspace root; anything else is rejected. -/
def resolveInWorkspace (root : System.FilePath) (rel : String) : Option System.FilePath :=
  if rel.startsWith "/" then none
  else if (rel.splitOn "/").any (· == "..") then none
  else some (root / rel)

def pathRejectedMsg : String := "path must be relative, no .."

/-- `mkdirs (Filename.dirname abs)` — create every missing parent directory
of `p` before writing to it. -/
def ensureParentDir (p : System.FilePath) : IO Unit := do
  match p.parent with
  | some parent => try IO.FS.createDirAll parent catch _ => pure ()
  | none => pure ()

/-! ### write_file -/

def writeFileTool : Mcp.Tool := {
  name := "write_file"
  description :=
    "Create or overwrite a file in the project workspace. Path is relative to the workspace root " ++
    "(e.g. Putnam/Helper.lean). Parent directories are created automatically."
  inputSchema := Json.mkObj [
    ("type", "object"),
    ("properties", Json.mkObj [
      ("path", Json.mkObj [("type", "string")]),
      ("content", Json.mkObj [("type", "string")])]),
    ("required", Json.arr #["path", "content"])
  ]
  handler := fun args => do
    match ← workspaceRoot? with
    | none => pure (Mcp.textResult workspaceNotSetMsg (isError := true))
    | some root =>
      match args.getObjValD "path" with
      | .str path =>
        match args.getObjValD "content" with
        | .str content =>
          match resolveInWorkspace root path with
          | none => pure (Mcp.textResult pathRejectedMsg (isError := true))
          | some abs =>
            ensureParentDir abs
            IO.FS.writeFile abs content
            pure (Mcp.textResult s!"wrote {path} ({content.toUTF8.size} bytes)")
        | _ => pure (Mcp.textResult "missing required argument: content" (isError := true))
      | _ => pure (Mcp.textResult "missing required argument: path" (isError := true))
}

/-! ### read_file -/

def readFileTool : Mcp.Tool := {
  name := "read_file"
  description := "Read a file from the workspace (relative path)."
  inputSchema := Json.mkObj [
    ("type", "object"),
    ("properties", Json.mkObj [("path", Json.mkObj [("type", "string")])]),
    ("required", Json.arr #["path"])
  ]
  handler := fun args => do
    match ← workspaceRoot? with
    | none => pure (Mcp.textResult workspaceNotSetMsg (isError := true))
    | some root =>
      match args.getObjValD "path" with
      | .str path =>
        match resolveInWorkspace root path with
        | none => pure (Mcp.textResult pathRejectedMsg (isError := true))
        | some abs =>
          if !(← abs.pathExists) then
            pure (Mcp.textResult s!"no such file: {path}" (isError := true))
          else
            pure (Mcp.textResult (← IO.FS.readFile abs))
      | _ => pure (Mcp.textResult "missing required argument: path" (isError := true))
}

/-! ### list_dir -/

/-- Every regular file under `root` (paths relative to `root`, `/`-joined,
sorted per directory level), skipping any entry whose name starts with `.`
(this subsumes the OCaml original's `_build`/dotfile skip: `.lake` — the
Lean analogue of `_build` — already starts with `.`). -/
partial def walkWorkspace (root : System.FilePath) (rel : String) : IO (Array String) := do
  let dir := if rel == "" then root else root / rel
  let entries ← (try dir.readDir catch _ => pure #[])
  let sorted := entries.qsort (fun a b => decide (a.fileName < b.fileName))
  let mut acc : Array String := #[]
  for e in sorted do
    let name := e.fileName
    unless name.startsWith "." do
      let r := if rel == "" then name else rel ++ "/" ++ name
      if (← e.path.isDir) then
        acc := acc ++ (← walkWorkspace root r)
      else
        acc := acc.push r
  return acc

def listDirTool : Mcp.Tool := {
  name := "list_dir"
  description := "List the workspace tree (paths relative to the root)."
  inputSchema := Json.mkObj [("type", "object"), ("properties", Json.mkObj [])]
  handler := fun _ => do
    match ← workspaceRoot? with
    | none => pure (Mcp.textResult workspaceNotSetMsg (isError := true))
    | some root =>
      let files ← walkWorkspace root ""
      pure (Mcp.textResult
        (if files.isEmpty then "(empty workspace)" else String.intercalate "\n" files.toList ++ "\n"))
}

/-! ### shared build lock (`lake_build`, `verify`)

A40 robustness note carried over from the OCaml original: concurrent `lake
build`s on one workspace race on Lake's own build lock (the loser errors
confusingly), so both tools that shell out to `lake build` serialize on this
file-based lock first — callers queue instead of failing. See the module
doc for why this needs a staleness clock where `Unix.lockf` would not. -/

private def buildLockPath (root : System.FilePath) : System.FilePath := root / ".team_build_lock"

private partial def acquireBuildLock (root : System.FilePath) (waitBudgetMs staleMs : Nat) : IO Unit := do
  let lp := buildLockPath root
  let pid ← IO.Process.getPID
  let startMs ← IO.monoMsNow
  let rec loop : IO Unit := do
    let already ← lp.pathExists
    if !already then
      let nowMs ← IO.monoMsNow
      let tmp := root / s!".team_build_lock.tmp.{pid}.{nowMs}"
      let claimed ←
        try
          IO.FS.writeFile tmp (toString nowMs)
          IO.FS.rename tmp lp
          pure true
        catch _ =>
          (try IO.FS.removeFile tmp catch _ => pure ())
          pure false
      if claimed then
        return ()
      else
        let elapsed ← IO.monoMsNow
        if elapsed - startMs > waitBudgetMs then return () else do IO.sleep 200; loop
    else
      let contentOpt ← (try some <$> IO.FS.readFile lp catch _ => pure none)
      let nowMs ← IO.monoMsNow
      let stale :=
        match contentOpt with
        | none => true
        | some c =>
          match c.trimAscii.copy.toNat? with
          | some t => nowMs - t > staleMs
          | none => true
      if stale then
        (try IO.FS.removeFile lp catch _ => pure ())
        loop
      else
        let elapsed ← IO.monoMsNow
        if elapsed - startMs > waitBudgetMs then return () else do IO.sleep 200; loop
  loop

private def releaseBuildLock (root : System.FilePath) : IO Unit :=
  try IO.FS.removeFile (buildLockPath root) catch _ => pure ()

/-- `lake build` at `root`, serialized by `acquireBuildLock`/`releaseBuildLock`. -/
def runLakeBuild (root : System.FilePath) (timeoutS : Float) : IO Proc.Result := do
  let staleMs := ((timeoutS + 300.0) * 1000.0).toUInt64.toNat
  let waitMs := ((timeoutS + 60.0) * 1000.0).toUInt64.toNat
  acquireBuildLock root waitMs staleMs
  let r ← Proc.run "lake" #["build"] (cwd := some root) (timeoutS := timeoutS)
  releaseBuildLock root
  pure r

/-! ### lake_build -/

def lakeBuildTool : Mcp.Tool := {
  name := "lake_build"
  description := "Run `lake build` at the workspace root and return its full output (all errors across all files)."
  inputSchema := Json.mkObj [("type", "object"), ("properties", Json.mkObj [])]
  handler := fun _ => do
    match ← workspaceRoot? with
    | none => pure (Mcp.textResult workspaceNotSetMsg (isError := true))
    | some root =>
      let r ← runLakeBuild root 240.0
      let suffix := if r.timedOut then " (TIMEOUT)" else ""
      pure (Mcp.textResult s!"exit code: {r.exitCode}{suffix}\n{r.output}"
        (log :=
          [ ("prover_ms", toJson r.durMs.toFloat)
          , ("exit_code", toJson r.exitCode)
          , ("timed_out", toJson r.timedOut) ]))
}

/-! ### verify: forbidden-token scan + clean build -/

/-- The harness gate's forbidden-token list (AF_TOOLS_SPEC.md §1) — NOT
`import`, since a freshly-written file legitimately needs one. -/
def forbiddenTokens : List String :=
  [ "sorry", "admit", "axiom", "native_decide", "set_option", "run_tac", "run_cmd",
    "#eval", "#exit", "unsafe", "implemented_by", "extern", "ofReduceBool", "ofReduceNat",
    "sorryAx", "addDecl", "addDeclWithoutChecking", "+native" ]

private def isIdentCh (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'

/-- Whether `tok` occurs in `body` with non-identifier characters (or the
string boundary) on both sides. -/
private def containsWordToken (body tok : String) : Bool := Id.run do
  let chars := body.toList.toArray
  let tokChars := tok.toList.toArray
  let n := chars.size
  let m := tokChars.size
  if m == 0 || m > n then return false
  let mut i := 0
  while i + m ≤ n do
    if chars.extract i (i + m) == tokChars then
      let beforeOk := i == 0 || !isIdentCh chars[i-1]!
      let afterOk := i + m == n || !isIdentCh chars[i+m]!
      if beforeOk && afterOk then return true
    i := i + 1
  return false

private def containsSubstr (body tok : String) : Bool := (body.splitOn tok).length > 1

/-- `#eval`/`#exit`/`+native` have no identifier boundary to speak of, so
they are matched as plain substrings; every other (identifier-shaped) token
is matched at word boundaries, mirroring the OCaml original's `\btok\b`. -/
private def containsForbidden (body tok : String) : Bool :=
  if tok.startsWith "#" || tok.startsWith "+" then containsSubstr body tok else containsWordToken body tok

/-- `(relative path, token)` for every forbidden token occurring in every
`.lean` file under `root` (skipping dot-entries, e.g. `.lake`) — one entry
per (file, token), first occurrence only, mirroring the OCaml original's
per-file `issues` accumulation. -/
partial def scanWorkspaceForbidden (root : System.FilePath) (rel : String) : IO (Array (String × String)) := do
  let dir := if rel == "" then root else root / rel
  let entries ← (try dir.readDir catch _ => pure #[])
  let sorted := entries.qsort (fun a b => decide (a.fileName < b.fileName))
  let mut acc : Array (String × String) := #[]
  for e in sorted do
    let name := e.fileName
    unless name.startsWith "." do
      let r := if rel == "" then name else rel ++ "/" ++ name
      if (← e.path.isDir) then
        acc := acc ++ (← scanWorkspaceForbidden root r)
      else if name.endsWith ".lean" then
        match (← try (some <$> IO.FS.readFile e.path) catch _ => pure none) with
        | none => pure ()
        | some src =>
          let body := Text.stripComments src
          for tok in forbiddenTokens do
            if containsForbidden body tok then
              acc := acc.push (r, tok)
  return acc

def verifyTool : Mcp.Tool := {
  name := "verify"
  description :=
    "Check the workspace AGAINST THE ACCEPTANCE GATE'S rules before you declare the project done: " ++
    "(1) scans every .lean file for forbidden tokens (sorry, admit, axiom, native_decide, set_option, " ++
    "run_tac, run_cmd, #eval, #exit, unsafe, implemented_by, extern, ofReduceBool, ofReduceNat, sorryAx, " ++
    "addDecl, addDeclWithoutChecking, +native — these REJECT the submission even if the build passes); " ++
    "(2) runs a clean `lake build`. Call this before replying DONE and fix everything it reports."
  inputSchema := Json.mkObj [("type", "object"), ("properties", Json.mkObj [])]
  handler := fun _ => do
    match ← workspaceRoot? with
    | none => pure (Mcp.textResult workspaceNotSetMsg (isError := true))
    | some root =>
      let hits ← scanWorkspaceForbidden root ""
      let issues := hits.toList.map (fun (f, tok) => s!"{f}: forbidden token `{tok}`")
      let r ← runLakeBuild root 240.0
      let buildOk := r.exitCode == 0
      if issues.isEmpty && buildOk then
        pure (Mcp.textResult "VERIFY OK: build clean, no forbidden tokens. Safe to reply DONE." (log := [("ok", toJson true)]))
      else
        let issueLines := String.intercalate "\n" (issues.map (fun x => "- " ++ x))
        let buildPart :=
          if buildOk then "" else "\n- lake build FAILS:\n" ++ String.mk (r.output.toList.take 2500)
        pure (Mcp.textResult s!"VERIFY FAILED — fix before DONE:\n{issueLines}{buildPart}" (log := [("ok", toJson false)]))
}

/-! ### tool registry -/

def main : IO Unit := Mcp.run [writeFileTool, readFileTool, listDirTool, lakeBuildTool, verifyTool]
