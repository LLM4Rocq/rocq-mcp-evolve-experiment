/-
Tests.Text — suite T: pure unit checks against `LeanMcpEvolve.Text`, no
server involved. Ports every case of `prototype-python/tests/test_text.py`
(12 test methods, see `prototype-python/tests/ARCHITECTURE.md`) with the SAME
assertions, adapted only where the Lean API genuinely has no literal
equivalent to the Python one:

  * there is no `split_statement` — `Decl.style` (already computed by
    `findDecls`, from the real parse) plus `statementText src d` is the
    equivalent (see docs/PLAN.md's note on `Tests/Text.lean`), and is used
    directly against the *original* source rather than a re-sliced /
    re-parsed substring, which is strictly more faithful;
  * `Decl` has no `kw_line` (the line of the bare keyword, excluding a
    folded doc-comment/attribute/`set_option ... in` prefix) — only
    `startLine`/`endLine` (which already fold those prefixes into the
    command, exactly like Python's `start_line`), so the `kw_line`
    sub-assertion of the Python `test_find_decls_names_and_extents` case has
    no Lean counterpart and is dropped (noted inline);
  * `header_end_line` returns a 0-based *line* index in Python; `headerEnd`
    returns a `String.Pos.Raw` *byte offset* in Lean — ported as "slicing the
    source from 0 to `headerEnd` yields exactly the header text", which is
    the same fact stated as a position rather than a line count;
  * `truncate`'s argument order is swapped (`n` first) per `Text.lean`'s own
    signature;
  * unlike the Python original (whose `find_decls`/`split_statement` are
    pure regexes, needing no real module resolution), `findDecls` runs
    Lean's own `processHeader`, which — confirmed empirically — degrades to
    an essentially empty environment (no `Init`, so not even `by`-blocks
    parse) when the file's *own* stated imports fail to resolve. Suite T
    intentionally runs without Mathlib on `LEAN_PATH` (see
    `tests/ARCHITECTURE.md`'s "suite T ... needs only Text.lean"), so `SRC`'s
    header uses `import Init` (always resolvable, unlike the Python
    fixture's `import Mathlib`) and `baz` uses `theorem` rather than the
    Python fixture's `lemma` (a Mathlib/Batteries macro, unavailable here) —
    both substitutions preserve every positional/structural property the
    original assertions exercise (the folded doc-comment/attribute prefix,
    the folded `set_option ... in`, line extents, `:= by`/term/pattern
    styles), they just use a resolvable stand-in import and a builtin
    keyword instead of the Mathlib-specific one. `importsOf`/`headerEnd`
    assertions are updated to match (`Init` instead of `Mathlib`).
-/
import Tests.Helpers
import LeanMcpEvolve.Text
import LeanMcpEvolve.Driver

namespace Tests.Text

open Lean (Environment)
open Tests.Helpers (Stats check contains)
open LeanMcpEvolve.Text

private def SRC : String :=
  "import Init\n\nopen Nat\n\nnamespace Foo\n\n/-- doc -/\n@[simp]\n" ++
  "theorem bar (n : Nat) : n + 0 = n := by\n  simp\n\n" ++
  "set_option maxHeartbeats 400 in\ntheorem baz (n : Nat) : 0 + n = n := by\n  sorry\n\n" ++
  "example : True := trivial\n\n" ++
  "def f (n : Nat) : Nat := n\n\n" ++
  "theorem qux : f 1 = 1 := rfl -- comment with := by\n\n" ++
  "theorem pat : ∀ n : Nat, n = n\n  | 0 => rfl\n  | n+1 => rfl\n\n" ++
  "end Foo\n\n" ++
  "theorem trailing (x : Nat) (h : x = x /- (:= by) -/) : x ≤ x := by\n  exact le_refl x\n"

/-- A throwaway `Environment` sufficient for `splitUnits`: this toolchain's
built-in tactic parsers (`induction`, `simp`, `constructor`, bullets, ...)
are registered process-wide when this program links `Lean`, independent of
what `env` has imported (confirmed empirically: `mkEmptyEnvironment` parses
them identically to an `Init`-importing environment) — only genuinely
macro-registered, import-gated tactics (Mathlib's `nlinarith`, say) actually
depend on `env`'s own import list, and precisely because this env has none,
`splitUnits` falls back to its line-based splitter exactly where the Python
prototype's own (always line/indentation-based) `split_units` would, making
this the environment that best reproduces the Python suite's behaviour
without requiring Mathlib to run suite T. -/
def mkEnv : IO Environment := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.mkEmptyEnvironment

/-- A real `import Init`-backed `Environment` (core Lean only, no Mathlib --
same `processHeader` technique `findDecls` itself uses, see its doc
comment), for `Driver.suggestNames` (T15/T16 below): unlike `mkEnv`'s
`mkEmptyEnvironment`, this one's `env.constants` actually contains core
declarations (`Nat.succ`, `Nat.add_zero`, ...) for the fuzzy near-miss
search to scan. -/
def mkInitEnv : IO Environment := do
  let inputCtx := Lean.Parser.mkInputContext "import Init\n" "<input>"
  let (header, _, _) ← Lean.Parser.parseHeader inputCtx
  let (env0, _) ← Lean.Elab.processHeader header {} {} inputCtx
  pure env0

def run (statsRef : IO.Ref Stats) : IO Unit := do
  let env ← mkEnv

  -- T1 — find_decls names/extents (test_find_decls_names_and_extents)
  let ds ← findDecls SRC
  let names := ds.toList.map (·.fullName)
  check statsRef (names == ["Foo.bar", "Foo.baz", "example", "Foo.f", "Foo.qux", "Foo.pat", "trailing"])
    "T1 findDecls names" s!"{names}"
  match findDecl ds "bar" with
  | none => check statsRef false "T1 findDecl bar found"
  | some bar =>
    -- kw_line has no Lean equivalent (see module doc); startLine/endLine do.
    check statsRef (bar.startLine == 6) "T1 bar.startLine == 6 (doc comment + attribute folded in)" s!"{bar.startLine}"
    check statsRef (bar.endLine == 9) "T1 bar.endLine == 9" s!"{bar.endLine}"
  match findDecl ds "Foo.baz" with
  | none => check statsRef false "T1 findDecl Foo.baz found"
  | some baz =>
    check statsRef (baz.startLine == 11) "T1 baz.startLine == 11 (set_option ... in folded in)" s!"{baz.startLine}"
  match findDecl ds "Foo.pat" with
  | none => check statsRef false "T1 findDecl Foo.pat found"
  | some pat => check statsRef (pat.endLine == 23) "T1 pat.endLine == 23" s!"{pat.endLine}"
  check statsRef ((findDecl ds "nope").isNone) "T1 findDecl nope == none"

  -- T2 — split-statement styles, via Decl.style + statementText on SRC itself
  -- (test_split_statement_styles)
  match findDecl ds "Foo.baz" with
  | none => check statsRef false "T2 findDecl Foo.baz found"
  | some baz =>
    check statsRef (baz.style == .«by») "T2 baz.style == by" s!"{repr baz.style}"
    let stmt := statementText SRC baz
    check statsRef (stmt.endsWith ":= by") "T2 baz statement ends with := by" stmt
  match findDecl ds "Foo.qux" with
  | none => check statsRef false "T2 findDecl Foo.qux found"
  | some qux => check statsRef (qux.style == .term) "T2 qux.style == term" s!"{repr qux.style}"
  match findDecl ds "Foo.pat" with
  | none => check statsRef false "T2 findDecl Foo.pat found"
  | some pat => check statsRef (pat.style == .pattern) "T2 pat.style == pattern" s!"{repr pat.style}"
  match findDecl ds "trailing" with
  | none => check statsRef false "T2 findDecl trailing found"
  | some trailing =>
    check statsRef (trailing.style == .«by») "T2 trailing.style == by" s!"{repr trailing.style}"
    let stmt := statementText SRC trailing
    check statsRef (contains stmt "/- (:= by) -/") "T2 trailing statement keeps commented := by" stmt

  -- T3 — a `:=` inside a parameter default value is not the split point
  -- (test_split_statement_default_arg)
  let src3 := "theorem t (n : ℕ := 0) : n = n := by\n  rfl"
  let ds3 ← findDecls src3
  match findDecl ds3 "t" with
  | none => check statsRef false "T3 findDecl t found"
  | some d3 =>
    let stmt3 := statementText src3 d3
    check statsRef (stmt3 == "theorem t (n : ℕ := 0) : n = n := by") "T3 default-arg statement" stmt3

  -- T4 — units by indentation and alternatives (test_units_by_indentation_and_alternatives)
  let bigText :=
    "by\n  intro n\n  induction n with\n  | zero => rfl\n  | succ n ih =>\n    simp\n    omega\n" ++
    "  constructor\n  · simp\n    ring\n  · nlinarith [sq_nonneg (x - y),\n      sq_nonneg (x + y)]\n  exact foo\n    bar"
  match splitUnits env bigText with
  | .error e => check statsRef false "T4 splitUnits parses" e
  | .ok u =>
    check statsRef (u.size == 6) "T4 splitUnits size == 6" s!"{u.toList}"
    check statsRef ((u.getD 1 "").startsWith "induction n with\n| zero") "T4 u[1] induction alt" (u.getD 1 "")
    check statsRef (u.getD 3 "" == "· simp\n  ring") "T4 u[3] bullet block" (u.getD 3 "")
    check statsRef ((u.getD 4 "").startsWith "· nlinarith [" && (u.getD 4 "").endsWith "]")
      "T4 u[4] bracket-continued bullet" (u.getD 4 "")
    check statsRef (u.getD 5 "" == "exact foo\n  bar") "T4 u[5] continuation line" (u.getD 5 "")

  -- T5 — leading `by` and semicolons (test_units_leading_by_and_semicolons)
  match splitUnits env "  by simp" with
  | .error e => check statsRef false "T5 splitUnits '  by simp'" e
  | .ok u => check statsRef (u == #["simp"]) "T5 splitUnits '  by simp' == [simp]" s!"{u.toList}"
  match splitUnits env "simp; ring" with
  | .error e => check statsRef false "T5 splitUnits 'simp; ring'" e
  | .ok u => check statsRef (u == #["simp; ring"]) "T5 splitUnits 'simp; ring' == [simp; ring]" s!"{u.toList}"
  match splitUnits env "\n\n  \n" with
  | .error e => check statsRef false "T5 splitUnits blank" e
  | .ok u => check statsRef (u == #[]) "T5 splitUnits blank == []" s!"{u.toList}"

  -- T6 — indent_block (test_indent_block)
  check statsRef (indentBlock #["a", "b\n  c"] "  " == "  a\n  b\n    c") "T6 indentBlock"

  -- T7 — strip_comments preserves offsets (test_strip_comments_preserves_offsets)
  let src7 := "x -- c\n/- a /- b -/ c -/ y \"-- not\" z"
  let out7 := stripComments src7
  check statsRef (out7.length == src7.length) "T7 stripComments preserves length"
    s!"{out7.length} vs {src7.length}"
  let expectedFirstLine7 := "x " ++ String.mk (List.replicate 4 ' ')
  check statsRef ((out7.splitOn "\n").headD "" == expectedFirstLine7) "T7 stripComments first line" (out7.splitOn "\n" |>.headD "")
  check statsRef (contains out7 "\"-- not\"") "T7 stripComments keeps string literal" out7
  check statsRef (!contains out7 "/-") "T7 stripComments removes block comment markers" out7

  -- T8 — forbidden scan ignores comments and strings (test_forbidden_scan_ignores_comments_and_strings)
  let src8 := "theorem x : True := by\n  sorry -- sorry\n/- axiom -/\n#eval \"sorry\"\nnative_decide\n"
  let hits8 := scanForbidden src8
  check statsRef (hits8 == [("sorry", 2), ("native_decide", 5)]) "T8 scanForbidden ignores comments/strings" s!"{hits8}"

  -- T9 — desync exploit regression (test_desync_exploit_regression, rocq-mcp-evolve D4)
  let src9 := "#eval \"/-\"\ntheorem x : True := by\n  sorry\n"
  let hits9 := scanForbidden src9
  check statsRef (hits9 == [("sorry", 3)]) "T9 scanForbidden desync regression" s!"{hits9}"

  -- T10 — Try this: parsing (test_try_this)
  check statsRef (parseTryThis "Try this:\n  [apply] exact Nat.le_add_right b 2" == some "exact Nat.le_add_right b 2")
    "T10 parseTryThis bracket tag"
  check statsRef (parseTryThis "Try this: simp only [foo]" == some "simp only [foo]") "T10 parseTryThis single line"
  check statsRef (parseTryThis "nothing here" == none) "T10 parseTryThis none"

  -- T11 — imports and header (test_imports_and_header)
  check statsRef (importsOf SRC == ["Init"]) "T11 importsOf SRC" s!"{importsOf SRC}"
  check statsRef (String.Pos.Raw.extract SRC ⟨0⟩ (headerEnd SRC) == "import Init\n")
    "T11 headerEnd SRC (one header line)" (String.Pos.Raw.extract SRC ⟨0⟩ (headerEnd SRC))
  let src11b := "-- c\nimport A\nimport B.C\n\nopen X\nimport D"
  check statsRef (importsOf src11b == ["A", "B.C"]) "T11 importsOf skips leading comment, stops at non-import" s!"{importsOf src11b}"

  -- T12 — truncate keeps head and tail (test_truncate_keeps_tail)
  let s12 := "head" ++ String.mk (List.replicate 100 'x') ++ "tail"
  let t12 := truncate 30 s12
  check statsRef (t12.startsWith "head" && t12.endsWith "tail" && contains t12 "elided") "T12 truncate keeps head/tail" t12

  -- T13/T14 — regression for the parser-scope bug: `findDecls` used to parse
  -- every command with a FIXED `ParserModuleContext` derived only from the
  -- header's imports, never applying a standalone `open`/`namespace`
  -- command's effect, so a `scoped` notation activated earlier in the file
  -- was not understood when parsing a later declaration (its `declVal`
  -- failed to parse, giving `DeclStyle.none`) -- real-world instance:
  -- PutnamBench files doing `open Nat` then `(n)!`, `open scoped Real` then
  -- `π`. Since `findDecls` never elaborates anything (see the function's
  -- own doc comment), a notation declared *in* the test source itself would
  -- never reach the environment either way, so unlike T1-T12 this needs a
  -- `scoped` notation that already exists via `import Init` alone (no
  -- Mathlib): `Init/Data/List/Basic.lean`'s `@[inherit_doc] scoped infixl:50
  -- " <+ " => List.Sublist`, declared inside `namespace List`.

  -- T13 — a standalone `open List` earlier in the file activates `<+` for a
  -- later declaration.
  let scopedOpenSrc :=
    "import Init\n\nopen List\n\ntheorem usesOpenSublist (l1 l2 : List Nat) : l1 <+ l2 := by\n  sorry\n"
  let dsOpen ← findDecls scopedOpenSrc
  match findDecl dsOpen "usesOpenSublist" with
  | none => check statsRef false "T13 findDecl usesOpenSublist found"
  | some d =>
    check statsRef (d.style == .«by»)
      "T13 open-activated scoped notation: declVal parses (style == by), not none" s!"{repr d.style}"

  -- T14 — `namespace X ... end X` with a `scoped` notation active *inside*
  -- `X` (entering `namespace List` re-activates `List`'s own scoped
  -- notations without needing an explicit `open`, matching
  -- `Lean/Elab/BuiltinCommand.lean`'s `addScope`); then a declaration after
  -- `end List` that still tries to use `<+` must go back to failing to
  -- parse it (style == none), proving `end` actually deactivates the scope
  -- again rather than leaking it for the rest of the file.
  let namespaceScopedSrc :=
    "import Init\n\nnamespace List\n\ntheorem innerUsesScoped (l1 l2 : List Nat) : l1 <+ l2 := by\n  sorry\n" ++
    "end List\n\ntheorem outerUsesScoped (l1 l2 : List Nat) : l1 <+ l2 := by\n  sorry\n"
  let dsNs ← findDecls namespaceScopedSrc
  match findDecl dsNs "List.innerUsesScoped" with
  | none => check statsRef false "T14 findDecl innerUsesScoped found"
  | some d =>
    check statsRef (d.style == .«by»)
      "T14 namespace-activated scoped notation: declVal parses inside the namespace (style == by)" s!"{repr d.style}"
  match findDecl dsNs "outerUsesScoped" with
  | none => check statsRef false "T14 findDecl outerUsesScoped found"
  | some d =>
    check statsRef (d.style == .«none»)
      "T14 `end` deactivates the scoped notation again (style == none outside the namespace)" s!"{repr d.style}"

  -- T15/T16 — `Driver.suggestNames`'s bounded did-you-mean search (LeanMcpEvolve
  -- design choices: the fuzzy scan over `env.constants` must return [] for
  -- short/generic names and stay bounded rather than scanning every constant
  -- unconditionally). Uses a real `import Init`-backed environment
  -- (`mkInitEnv`) so core names like `Nat.succ`/`Nat.add_zero` are actually
  -- present to be found — no Mathlib involved.
  let initEnv ← mkInitEnv

  -- T15 — short (< 3 char) unknown short names return [] immediately,
  -- whether or not the identifier is dotted.
  check statsRef (LeanMcpEvolve.Driver.suggestNames initEnv "u" == [])
    "T15 suggestNames 1-char ident returns []" s!"{LeanMcpEvolve.Driver.suggestNames initEnv "u"}"
  check statsRef (LeanMcpEvolve.Driver.suggestNames initEnv "ab" == [])
    "T15 suggestNames 2-char ident returns []" s!"{LeanMcpEvolve.Driver.suggestNames initEnv "ab"}"
  check statsRef (LeanMcpEvolve.Driver.suggestNames initEnv "Nat.ab" == [])
    "T15 suggestNames 2-char short name (dotted) returns []" s!"{LeanMcpEvolve.Driver.suggestNames initEnv "Nat.ab"}"

  -- T16 — a typo of an existing core name is still suggested (bounded scan
  -- doesn't drop legitimate near-misses).
  let sugg16 := LeanMcpEvolve.Driver.suggestNames initEnv "Nat.sucx"
  check statsRef (sugg16.contains "Nat.succ") "T16 suggestNames Nat.sucx suggests Nat.succ" s!"{sugg16}"

end Tests.Text
