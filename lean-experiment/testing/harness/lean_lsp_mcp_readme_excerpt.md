<!-- Frozen excerpt of the sibling lean-lsp-mcp server's documentation (its
     Key Features blurb, MCP Tools reference from docs/tools.md, and the
     server's own `initialize.instructions` string as captured by
     capture_handshake.py -- operator/deployment sections (Setup, MCP
     Configuration, transports, REPL, containerized setup, etc.) excluded,
     mirroring the A60 documentation rule rocq-mcp-evolve's
     harness/sota_readme_excerpt.md applied to rocq-mcp's README.
     Source: https://github.com/oOo0oOo/lean-lsp-mcp (README.md +
     docs/tools.md), fetched 2026-09-08. Installed version at fetch time:
     0.30.0 (`uvx lean-lsp-mcp --version`; matches the captured handshake's
     serverInfo.version in lean_lsp_mcp_handshake_cache.json). NOT injected
     into any prompt in this port (see testing/README.md, "Arms:
     compiler-only control and lean-lsp-mcp sibling in the workspace
     setting" -- the AF_TOOLS system-prompt paragraph for
     af_lean_lsp_mcp_prompted_sonnet_wallonly was written FROM this excerpt,
     not injected verbatim as a {readme} slot the way af3_sota did). -->

# lean-lsp-mcp

MCP server that allows agentic interaction with the [Lean theorem
prover](https://lean-lang.org/) via the [Language Server
Protocol](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/)
using [leanclient](https://github.com/oOo0oOo/leanclient). This server
provides a range of tools for LLM agents to understand, analyze and interact
with Lean projects.

## Key Features

* **Rich Lean Interaction**: Access diagnostics, goal states, term
  information, hover documentation and more.
* **External Search Tools**: Use `LeanSearch`, `Loogle`, `Lean Finder`, `Lean
  Hammer` and `Lean State Search` to find relevant theorems and definitions.
* **Easy Setup**: Simple configuration for various clients, including
  VSCode, Cursor and Claude Code.

## MCP Tools

(from `docs/tools.md`; all `file_path` arguments are absolute or
project-root-relative and resolve against the server's configured Lean
project -- see "Path Policy" below)

### File interactions (LSP)

- **lean_file_outline** -- Get a concise outline of a Lean file showing
  imports and declarations with type signatures (theorems, definitions,
  classes, structures).
- **lean_diagnostic_messages** -- Get all diagnostic messages for a Lean
  file (infos, warnings, errors). `severity` filters to one level.
  `interactive=True` returns verbose nested `TaggedText` with embedded
  widgets; for "Try This" suggestions prefer `lean_code_actions`.
- **lean_goal** -- Get the proof goal at a specific location (line, or line
  & column) in a Lean file. Omitting `column` returns goals_before /
  goals_after (state at line start / end); `status` is `'goals'`,
  `'complete'` (proof finished here), or `'no_goal_at_position'`.
- **lean_term_goal** -- Get the expected (term) type at a specific position
  (line & column).
- **lean_hover_info** -- Retrieve hover information (type signature + docs)
  for a symbol/term at a specific position.
- **lean_declaration_file** -- Get the file contents where a symbol or term
  is declared (`full_file=True` for the whole file -- can be large).
- **lean_references** -- Find all references to a symbol at a position,
  including its declaration.
- **lean_completions** -- Code auto-completion: identifiers or import
  suggestions available at a position (use on incomplete code, e.g. after
  `.` or a partial name).
- **lean_run_code** -- Run/compile an independent, self-contained Lean code
  snippet (must include its own imports) and return diagnostics.
- **lean_multi_attempt** -- Attempt multiple tactic snippets at a proof
  position WITHOUT modifying the file; returns the goal state and
  diagnostics for each -- screen several candidates before committing one.
  `column` targets an exact source position; omit it for fast line-based
  attempts.
- **lean_code_actions** -- LSP code actions for a line: resolved edits for
  "Try This" suggestions (`simp?`, `exact?`, `apply?`) and other quick
  fixes; the agent applies the edits itself.
- **lean_get_widgets** / **lean_get_widget_source** -- panel widgets (proof
  visualizations, `#html`) at a position, and a widget's JS source by hash.
- **lean_profile_proof** -- Run `lean --profile` on an isolated copy of a
  theorem; per-line timing and categories. SLOW.
- **lean_verify** -- Check theorem soundness: axioms used (standard three
  are `propext`, `Classical.choice`, `Quot.sound` -- anything else, e.g.
  `sorryAx`, indicates an unsound proof) plus an optional source-pattern
  scan (`unsafe`, `set_option debug.*`, `@[implemented_by]`, etc; requires
  `ripgrep`).
- **lean_minimal_hypotheses** -- For each explicit `(h : T)` hypothesis of a
  theorem, drop it and re-elaborate via the LSP; reports which are
  load-bearing (with the resulting errors) vs. actually unused. SLOW (one
  full re-elaboration per hypothesis).

### Local Search Tools

- **lean_local_search** -- Search Lean definitions/theorems in the local
  project and stdlib; confirms a declaration actually exists before you
  reference it. Requires `ripgrep`.

### External Search Tools (rate-limited, "please don't overuse these free
services")

- **lean_leansearch** (natural-language search via leansearch.net, 90
  req/30s) -- natural language, mixed queries, concepts, identifiers, or
  Lean terms, e.g. `"bijective map from injective"`, `List.sum`.
- **lean_loogle** (type-pattern search via loogle.lean-lang.org, 3 req/30s
  remote / unlimited with `--loogle-local`) -- by constant, lemma name,
  subexpression, type, or conclusion, e.g. `Real.sin`, `_ * (_ ^ _)`,
  `|- tsum _ = _ * tsum _`.
- **lean_leanfinder** (semantic search via Lean Finder, 10 req/30s) --
  informal descriptions, questions, proof states, or statement fragments;
  `version` selects a mathlib snapshot (`v4.19.0`/`v4.24.0`/`v4.28.0`,
  default latter).
- **lean_state_search** (premise-search.com, 6 req/30s) -- applicable
  theorems for the goal at a given line & column.
- **lean_hammer_premise** (Lean Hammer Premise Search, 6 req/30s) --
  relevant premises (for `simp`/`aesop`/hints) for the goal at a line &
  column.

### Project-level tools

- **lean_build** -- Run `lake build` and restart the LSP. Optional
  `clean=true` (slow, `lake clean` first) and `fetch_cache=true` (slow,
  `lake exe cache get` first, for missing dependency caches). Only needed
  after new imports; SLOW.

## Server's own instructions (from the captured MCP handshake --
`initialize.instructions`, `lean_lsp_mcp_handshake_cache.json`)

> ## General Rules
> - All line and column numbers are 1-indexed. Columns count characters
>   (codepoints).
> - This MCP does NOT edit files. Use other tools for editing.
>
> ## Key Tools
> - **lean_goal**: Proof state at position. Omit `column` for before/after.
>   `status` field: 'goals', 'complete' (proof done here), or
>   'no_goal_at_position' (not inside a proof).
> - **lean_diagnostic_messages**: Compiler errors/warnings. "no goals to be
>   solved" = remove tactics.
> - **lean_term_goal**: Expected type at a position.
> - **lean_hover_info**: Type signature + docs. Column at START of
>   identifier.
> - **lean_completions**: IDE autocomplete on incomplete code.
> - **lean_local_search**: Fast local declaration search. Use BEFORE trying
>   a lemma name.
> - **lean_file_outline**: Token-efficient file skeleton (slow-ish).
> - **lean_multi_attempt**: Test tactics without editing at a proof
>   position. Use `column` for an exact source position; omit it for fast
>   line-based attempts: `["simp", "ring", "omega"]`
> - **lean_code_actions**: Quick fixes and `TryThis` suggestions (simp?,
>   exact?) with resolved edits.
> - **lean_declaration_file**: Declaration source slice with context;
>   `full_file=true` for the whole file (large).
> - **lean_references**: All usages of a symbol (capped by `max_results`,
>   `total` reports the full count).
> - **lean_run_code**: Run standalone snippet. Must include imports.
> - **lean_verify**: Axiom check + source scan. Use fully qualified name
>   (e.g. `Ns.thm`).
> - **lean_minimal_hypotheses**: Which explicit hypotheses of a theorem are
>   actually needed.
> - **lean_build**: Run `lake build` + restart LSP. Only if needed (new
>   imports). Use `fetch_cache=true` only for missing dependency caches.
>   SLOW!
> - **lean_profile_proof**: Profile a theorem for performance. Shows tactic
>   hotspots. SLOW!
>
> ## Search Tools (rate limited)
> - **lean_leansearch** (90/30s): Natural language -> mathlib
> - **lean_loogle** (3/30s): Type pattern -> mathlib
> - **lean_leanfinder** (10/30s): Semantic/conceptual search
> - **lean_state_search** (6/30s): Goal -> closing lemmas
> - **lean_hammer_premise** (6/30s): Goal -> premises for simp/aesop
>
> ## Search Decision Tree
> 1. "Does X exist locally?" -> lean_local_search
> 2. "I need a lemma that says X" -> lean_leansearch
> 3. "Find lemma with type pattern" -> lean_loogle
> 4. "What's the Lean name for concept X?" -> lean_leanfinder
> 5. "What closes this goal?" -> lean_state_search
> 6. "What to feed simp?" -> lean_hammer_premise
>
> After finding a name: lean_local_search to verify, lean_hover_info for
> signature.
>
> ## Return Formats
> List-returning tools return an object with an `items` array. Empty =
> `{"items": []}`.
>
> ## Slow Files
> On large files, pass `timeout_s` to lean_diagnostic_messages / lean_goal.
> A response with `partial: true` + `still_elaborating_lines` (or goal
> `status: 'still_elaborating'`) means Lean is still working - poll again;
> it is NOT an error or a dead server.
>
> ## Error Handling
> Check `isError` in responses: `true` means failure (timeout/LSP
> error/rate limit), while an empty `items` with `isError: false` means no
> results found.

## Path Policy

File-based tools only operate on files inside the active Lean project,
resolved `.lake/packages/*` dependencies, and the Lean stdlib source tree.
Returned file paths are sanitized to avoid leaking host absolute paths:
project files relative to the project root (e.g. `src/MyFile.lean`),
dependency files under `.lake/packages/<package>/...`, stdlib files under
`.lean-stdlib/...`. Symlink escapes outside those roots are rejected.
