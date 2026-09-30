import Lean.Data.Json
import Lean.Data.JsonRpc
import Std.Time.DateTime.Timestamp

/-!
Minimal MCP (Model Context Protocol) stdio server: newline-delimited
JSON-RPC 2.0, a tool registry, and JSONL instrumentation — ported from
`prototype-python/src/lean_mcp_evolve/mcp_server.py` (itself the same
`mcp_core` transport rocq-mcp-evolve uses), with the same wire behaviour and
message texts.

Transport note: MCP over stdio is newline-delimited JSON-RPC, *not*
Content-Length-framed LSP messages, so this reads/writes raw lines rather
than using `IO.FS.Stream.readLspMessage`/`writeLspMessage`. `Lean.JsonRpc`'s
`Message`/`RequestID`/`ErrorCode` types are used for encoding responses;
incoming messages are read as plain `Lean.Json` and picked apart by hand
(mirroring the Python original's lenient `dict.get`-based dispatch, which
does not require every message to satisfy a strict request/notification
schema before being routed).
-/

namespace LeanMcpEvolve.Mcp

open Lean (Json ToJson toJson)

def serverName : String := "lean-mcp-evolve"
def serverVersion : String := "0.1.0"

/-- The result a tool handler produces: the text block(s) sent back to the
agent, whether it counts as an error, and any extra fields to splice into
the JSONL instrumentation record for this call. -/
structure ToolResult where
  text : String
  isError : Bool := false
  log : List (String × Json) := []

/-- One exposed tool: its MCP metadata plus the handler that runs it. The
handler receives the `arguments` object from `tools/call` (or `{}` if the
call carried none / a non-object). -/
structure Tool where
  name : String
  description : String
  inputSchema : Json
  handler : Json → IO ToolResult

def textResult (text : String) (isError : Bool := false) (log : List (String × Json) := []) :
    ToolResult :=
  { text, isError, log }

/-- Writes `msg` to stderr as `"[lean-mcp-evolve] msg"`, iff env
`LEAN_MCP_DEBUG` is set to a non-empty value. stdout carries only
JSON-RPC, so all server-side tracing goes here. -/
def debug (msg : String) : IO Unit := do
  match ← IO.getEnv "LEAN_MCP_DEBUG" with
  | some v =>
    if v.isEmpty then
      pure ()
    else do
      let stderr ← IO.getStderr
      stderr.putStr s!"[{serverName}] {msg}\n"
      stderr.flush
  | none => pure ()

-- --- instrumentation ------------------------------------------------------

/-- Lazily-opened `LEAN_LOG_FILE` handle, cached across calls; `some none`
means "checked, no log file configured". -/
initialize logHandleRef : IO.Ref (Option (Option IO.FS.Handle)) ← IO.mkRef none

/-- Lazily-parsed `LEAN_LOG_META` object, cached across calls. -/
initialize logMetaRef : IO.Ref (Option Json) ← IO.mkRef none

/-- Process-wide JSONL record counter. -/
initialize seqRef : IO.Ref Nat ← IO.mkRef 0

/-- Process-wide running total of wall-clock milliseconds spent loading
header environments (`LeanMcpEvolve.Driver.getHeaderState`, cache hit or
miss) -- README "Excluding Mathlib import time from attempt budgets". This is
what the `shutdown` record's `import_ms_total` reports (`getImportMsTotal`),
and what `handleToolsCall` diffs across one `tools/call` to produce that
call's own `import_ms` (the wall time THIS call spent waiting on imports,
whether a cache miss it triggered directly or a background prewarm task it
had to wait for finishing during the call). -/
initialize importMsTotalRef : IO.Ref Float ← IO.mkRef 0.0

/-- Add `ms` (a single header load's own duration, 0 on a cache hit) to the
process-wide import-time counter. Called from `Driver.getHeaderState`. -/
def addImportMs (ms : Float) : IO Unit := importMsTotalRef.modify (· + ms)

/-- The process-wide running total (see `importMsTotalRef`'s doc comment). -/
def getImportMsTotal : IO Float := importMsTotalRef.get

def openLogHandleFromEnv : IO (Option IO.FS.Handle) := do
  match ← IO.getEnv "LEAN_LOG_FILE" with
  | none => pure none
  | some path =>
    if path.isEmpty then
      pure none
    else
      try
        let h ← IO.FS.Handle.mk (System.FilePath.mk path) IO.FS.Mode.append
        pure (some h)
      catch e =>
        debug s!"could not open LEAN_LOG_FILE: {e}"
        pure none

def getLogHandle : IO (Option IO.FS.Handle) := do
  match ← logHandleRef.get with
  | some h => pure h
  | none =>
    let h ← openLogHandleFromEnv
    logHandleRef.set (some h)
    pure h

def parseLogMetaFromEnv : IO Json := do
  match ← IO.getEnv "LEAN_LOG_META" with
  | none => pure (Json.mkObj [])
  | some raw =>
    if raw.isEmpty then
      pure (Json.mkObj [])
    else
      match Json.parse raw with
      | .ok (j@(Json.obj _)) => pure j
      | _ => pure (Json.mkObj [])

def getLogMeta : IO Json := do
  match ← logMetaRef.get with
  | some j => pure j
  | none =>
    let j ← parseLogMetaFromEnv
    logMetaRef.set (some j)
    pure j

/-- Appends one JSONL record `{seq, ...fields, ...LEAN_LOG_META}` to
`LEAN_LOG_FILE` (a no-op if that env var is unset), flushing immediately.
`LEAN_LOG_META` fields win on key collisions with `fields`, matching the
Python original's `rec.update(meta)`. -/
def emitLog (fields : List (String × Json)) : IO Unit := do
  match ← getLogHandle with
  | none => pure ()
  | some h => do
    let seq ← seqRef.modifyGet (fun n => (n + 1, n + 1))
    let metaJson ← getLogMeta
    let rec_ := Json.mkObj (("seq", toJson seq) :: fields)
    let merged := rec_.mergeObj metaJson
    h.putStr (merged.compress ++ "\n")
    h.flush

/-- Wall-clock seconds since the Unix epoch, as a float (fractional part
from nanosecond precision). Unlike `IO.monoMsNow`/`IO.monoNanosNow`, which
are explicitly documented as having "no relation to wall clock time",
`Std.Time.Timestamp.now` is this toolchain's actual wall clock, so it is
used here despite `Mcp`'s otherwise minimal footprint. -/
def wallClockNow : IO Float := do
  let ts ← Std.Time.Timestamp.now
  let secs : Nat := ts.val.second.toInt.toNat
  let nanos : Nat := ts.val.nano.val.toNat
  pure (secs.toFloat + nanos.toFloat / 1000000000.0)

-- --- JSON-RPC plumbing ----------------------------------------------------

def send (msg : Lean.JsonRpc.Message) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr ((toJson msg).compress ++ "\n")
  stdout.flush

def toRequestId (j : Json) : Lean.JsonRpc.RequestID :=
  match j with
  | .str s => .str s
  | .num n => .num n
  | _ => .null

def toolJson (t : Tool) : Json :=
  Json.mkObj [("name", t.name), ("description", t.description), ("inputSchema", t.inputSchema)]

def handleToolsCall (tools : List Tool) (rid : Lean.JsonRpc.RequestID) (params : Json) : IO Unit := do
  let name := match params.getObjValD "name" with
    | .str s => s
    | _ => ""
  let argsJson := params.getObjValD "arguments"
  let args := match argsJson with
    | j@(Json.obj _) => j
    | _ => Json.mkObj []
  match tools.find? (fun t => t.name == name) with
  | none =>
    send (Lean.JsonRpc.Message.responseError rid .invalidParams s!"unknown tool: {name}" none)
  | some tool => do
    let t0 ← IO.monoMsNow
    let tsWall ← wallClockNow
    let importBefore ← getImportMsTotal
    let r ← try
        tool.handler args
      catch e =>
        pure (textResult s!"internal tool error: {e}" (isError := true))
    let t1 ← IO.monoMsNow
    let importAfter ← getImportMsTotal
    let durMs : Float := (t1 - t0).toFloat
    -- Wall time this CALL's handling spent on header/import loads: a cache
    -- miss it triggered directly, or a background prewarm task it waited on
    -- mid-call (`Driver.acquireHeaderState`) -- either way that work
    -- completes strictly within [t0, t1], so this counter's delta over the
    -- same window captures it exactly (README's import-timing deliverable).
    let importMs : Float := importAfter - importBefore
    let logFields : List (String × Json) :=
      [ ("ts", toJson tsWall), ("kind", Json.str "tool_call"), ("tool", Json.str name)
      , ("args", args), ("dur_ms", toJson durMs), ("is_error", Json.bool r.isError)
      , ("result_chars", toJson r.text.length), ("result", Json.str r.text)
      , ("import_ms", toJson importMs) ] ++ r.log
    emitLog logFields
    send (Lean.JsonRpc.Message.response rid (Json.mkObj
      [ ("content", Json.arr #[Json.mkObj [("type", Json.str "text"), ("text", Json.str r.text)]])
      , ("isError", Json.bool r.isError) ]))

def handleMessage (tools : List Tool) (msg : Json) : IO Unit := do
  let ridJson := msg.getObjValD "id"
  let rid := toRequestId ridJson
  let isNotification := ridJson == Json.null
  let method := match msg.getObjValD "method" with
    | .str s => s
    | _ => ""
  let paramsJson := msg.getObjValD "params"
  let params := match paramsJson with
    | j@(Json.obj _) => j
    | _ => Json.mkObj []
  match method with
  | "initialize" => do
    let clientJson := params.getObjValD "clientInfo"
    let pv := match params.getObjValD "protocolVersion" with
      | .str s => s
      | _ => "2024-11-05"
    let ts ← wallClockNow
    emitLog [("ts", toJson ts), ("kind", Json.str "initialize"), ("client", clientJson)]
    send (Lean.JsonRpc.Message.response rid (Json.mkObj
      [ ("protocolVersion", Json.str pv)
      , ("capabilities", Json.mkObj [("tools", Json.mkObj [])])
      , ("serverInfo", Json.mkObj
          [("name", Json.str serverName), ("version", Json.str serverVersion)]) ]))
  | "tools/list" =>
    send (Lean.JsonRpc.Message.response rid (Json.mkObj
      [("tools", Json.arr (tools.map toolJson).toArray)]))
  | "tools/call" => handleToolsCall tools rid params
  | "ping" => send (Lean.JsonRpc.Message.response rid (Json.mkObj []))
  | _ =>
    if isNotification || method.startsWith "notifications/" then
      pure ()
    else
      send (Lean.JsonRpc.Message.responseError rid .methodNotFound s!"method not found: {method}" none)

/-- Reads and serves one JSON-RPC message per line from `stdin`, forever
(until EOF). A handler exception never reaches here (`handleToolsCall`
catches it), but a bug elsewhere in dispatch is still contained so the
server keeps running. -/
partial def loop (tools : List Tool) (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then
    pure ()
  else
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then
      loop tools stdin
    else do
      match Json.parse trimmed with
      | .error _ =>
        send (Lean.JsonRpc.Message.responseError .null .parseError "parse error" none)
      | .ok j =>
        try
          handleMessage tools j
        catch e =>
          debug s!"unhandled error: {e}"
      loop tools stdin

/-- Serves MCP tool calls over stdio until stdin closes (EOF), then runs
`onExit`. stdout carries only JSON-RPC; everything else goes to stderr via
`debug`. -/
def run (tools : List Tool) (onExit : IO Unit := pure ()) : IO Unit := do
  let stdin ← IO.getStdin
  tryFinally (loop tools stdin) onExit

end LeanMcpEvolve.Mcp
