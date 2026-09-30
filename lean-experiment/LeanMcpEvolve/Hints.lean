/-
Phase 2c (see docs/PLAN.md §6 phase 2c). Verbatim port of the Python
reference `prototype-python/src/lean_mcp_evolve/hints.py`: the error-hint
table (Rocq/Coq-isms, Lean 3-isms, message-keyed rules) and the hint-term
synthesis for the `nlinarith`/`positivity` portfolio finishers.

Everything here is pure text processing except the three `LEAN_*` env-var
readers (`hintsOn`, `suggestOn`, `auto2On`), which are `IO Bool`. In
particular `hintFor`/`withHint` do NOT consult `LEAN_HINTS` themselves (the
Python `hint_for` does, via `hints_on()`, but the deliverable's own type
--`Option String`, not `IO (Option String)`-- rules that out for a pure
function); the caller (Driver, phase 2b/3) is expected to check `hintsOn`
first and only call `hintFor`/`withHint` when it is true, exactly as it must
read `auto2On` itself before deciding what `enabled` to pass to
`synthCandidates`.

`GoalFacts` differs from the Python `arith_vars`/`positivity_hyps`/
`power_terms`, which scan a *printed* goal string with regexes: here the
Driver computes the same facts from the `MetaM` local context and conclusion
directly (no goal string, no regex) and hands them to `synthCandidates`,
which only formats them into candidate scripts -- but it still performs the
even-power arithmetic (half-exponent, `b ^ h` vs bare `b`, the "- 1"/"+ 1"
pair, the de-duplication and the cap at 4) that Python's `power_terms` does,
since the Driver only supplies the raw `(base, exponent)` pairs found in the
conclusion.
-/

namespace LeanMcpEvolve.Hints

/-! ### env-var gates -/

def hintsOn : IO Bool := do
  return (← IO.getEnv "LEAN_HINTS") != some "0"

def suggestOn : IO Bool := do
  return (← IO.getEnv "LEAN_SUGGEST") != some "0"

def auto2On : IO Bool := do
  return (← IO.getEnv "LEAN_AUTO2") != some "0"

/-! ### small string helpers (avoid `String.trim`/`.drop`, which return
`String.Slice` on this toolchain -- see docs/PHASE1_NOTES.md pitfalls) -/

/-- Trim ASCII whitespace from both ends, always returning a `String`. -/
def trimStr (s : String) : String :=
  s.trimAscii.copy

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

private def isIdentCont (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || c == '\'' || c == '.' || c == '?' || c == '!'

/-- Leading identifier-ish token: letters, digits, `_ ' . ? !`, first char
must be a letter or `_` (port of Python's
`re.match(r"[A-Za-z_][A-Za-z0-9_'.?!]*", s.strip())`, falling back to the
first character when nothing matches, `""` on an empty string). -/
def firstWord (s : String) : String :=
  let s := trimStr s
  match s.toList with
  | [] => ""
  | c0 :: cs =>
    if isIdentStart c0 then
      String.ofList (c0 :: cs.takeWhile isIdentCont)
    else
      String.ofList [c0]

private def dedupe (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-! ### the foreign-tactic table -/

/-- Rocq / Coq / Lean 3 first words -> Lean 4 advice. Verbatim port of
`FOREIGN_TACTIC_MAP`, entries whose Python value is `None` (`tauto`,
`omega`) dropped -- they are recognised Lean 4 tactics, listed in the
Python table only to document that they need no rewrite. -/
def foreignTacticMap : List (String × String) := [
  -- Rocq / Coq
  ("intros", "Lean 4: `intro x y h` names the binders (`intros` takes no names and yields inaccessible ones)"),
  ("lia", "use `omega` (linear ℕ/ℤ arithmetic) or `linarith` (ordered fields)"),
  ("nia", "use `nlinarith` (or `omega` when the goal is linear after unfolding)"),
  ("lra", "use `linarith`"),
  ("nra", "use `nlinarith`, optionally with hints: `nlinarith [sq_nonneg (a - b)]`"),
  ("psatz", "use `nlinarith [sq_nonneg (a - b), mul_pos ha hb]` or `positivity`"),
  ("field", "use `field_simp` then `ring`"),
  ("ring_simplify", "use `ring_nf`"),
  ("reflexivity", "use `rfl`"),
  ("symmetry", "use `symm`"),
  ("auto", "use `simp`, `aesop`, `trivial`, or `exact?`"),
  ("eauto", "use `aesop` or `exact?`"),
  ("easy", "use `trivial`, `simp`, or `decide`"),
  ("firstorder", "use `aesop` or `tauto`"),
  ("destruct", "use `rcases h with ⟨a, b⟩` / `obtain ⟨a, b⟩ := h` / `cases h with | inl h => .. | inr h => ..`"),
  ("inversion", "use `cases h` (or `injection h`, `rcases h with ⟨⟩`)"),
  ("discriminate", "use `simp at h`, `contradiction`, `cases h`, or `exact absurd h (by decide)`"),
  ("assert", "use `have h : T := by ...` (or `have h : T := proof_term`)"),
  ("rewrite", "use `rw [h]`, `rw [← h]`, `rw [h] at h'` (brackets are mandatory)"),
  ("simpl", "use `simp only []`, `dsimp`, or `simp`"),
  ("exists", "use `use x` (Mathlib), `exact ⟨x, ?_⟩`, or `refine ⟨x, ?_⟩`"),
  ("split", "for `∧`/`↔` use `constructor` (`split` in Lean 4 is for `if`/`match` goals)"),
  ("pose", "use `let x := e` or `set x := e with hx`"),
  ("remember", "use `generalize hx : e = x`"),
  ("now", "Lean 4 has no `now`; write `tac <;> trivial` or `tac; trivial`"),
  ("Search", "there is no `Search`: as a step, `exact?` / `apply?` / `rw?` search the library, `#check foo` prints a statement"),
  ("Check", "as a step, write `#check foo` (a query; it is not committed)"),
  ("Print", "as a step, write `#print foo` (a query; it is not committed)"),
  ("Qed", "Lean has no `Qed` — the proof is complete once no goals remain"),
  ("Proof", "Lean has no `Proof.` — tactics follow `:= by` directly"),
  ("Admitted", "FORBIDDEN — incomplete proofs are rejected; find a real proof"),
  ("admit", "FORBIDDEN — incomplete proofs are rejected; find a real proof"),
  ("sorry", "FORBIDDEN — incomplete proofs are rejected; find a real proof"),
  -- Lean 3
  ("assume", "use `intro x`"),
  ("refl", "use `rfl`"),
  ("cases'", "prefer `obtain ⟨a, b⟩ := h` or `rcases h with ⟨a, b⟩`"),
  ("by_contradiction", "use `by_contra h`"),
  ("norm_num1", "use `norm_num`"),
  ("finish", "use `aesop`"),
  ("tidy", "use `aesop`"),
  ("library_search", "use `exact?`"),
  ("suggest", "use `apply?`"),
  ("unfold_coes", "use `push_cast` / `norm_cast`"),
  ("begin", "Lean 4 proofs start with `by` (no `begin ... end`)"),
]

/-- First words whose Lean-3 (rather than Rocq/Coq) origin is called out. -/
private def lean3Words : List String :=
  ["assume", "refl", "cases'", "by_contradiction", "finish", "tidy",
   "library_search", "suggest", "begin", "unfold_coes", "norm_num1"]

def toolNames : List String :=
  ["rollback", "state", "try", "step", "check", "build", "verify", "auto_close", "open"]

/-! ### unknown-name heuristics (port of the `kind == "unknown_ref"` branch) -/

private def quoteOpen : List Char := ['`', '\'', '‘']
private def quoteClose : List Char := ['`', '\'', '’']

/-- Port of `re.search(r"[`'‘]([^`'’\s]+)", head)`: the first non-empty run
of non-quote, non-whitespace characters following an opening quote char. -/
private partial def extractQuoted : List Char → Option String
  | [] => none
  | c :: rest =>
    if quoteOpen.contains c then
      let name := rest.takeWhile (fun ch => !quoteClose.contains ch && !ch.isWhitespace)
      if name.isEmpty then extractQuoted rest else some (String.ofList name)
    else extractQuoted rest

/-- Port of `re.match(r"^[A-Z][a-z]+_[a-z_]+$", name)`: uppercase, then
one-or-more lowercase, then a literal `_`, then one-or-more of
`[a-z_]`, the whole string consumed. -/
private def looksLikeCoqLemma (name : String) : Bool :=
  match name.toList with
  | [] => false
  | c0 :: rest =>
    if !c0.isUpper then false
    else
      let (lowers, rest1) := rest.span Char.isLower
      if lowers.isEmpty then false
      else match rest1 with
        | '_' :: rest2 => !rest2.isEmpty && rest2.all (fun c => c.isLower || c == '_')
        | _ => false

private def coqPrefixes : List String :=
  ["Rmult", "Rplus", "Rle", "Rlt", "Nat.add_comm_", "pow2_ge_0", "Rsqr"]

/-! ### `hint_for` -/

/-- Verbatim port of `hint_for` (same texts, same order of rules). Does not
itself gate on `LEAN_HINTS` -- see the module doc. -/
def hintFor (sentence msg kind : String) (available : Option (List (String × Bool)) := none) :
    Option String :=
  let w := firstWord sentence
  let head := (msg.splitOn "\n").headD msg
  if toolNames.contains w then
    some s!"`{w}` is a TOOL, not a tactic — call the {w} tool instead."
  else
  let unresolved := kind == "unknown_ref" || kind == "syntax" || head.contains "unknown tactic"
  match (unresolved, foreignTacticMap.lookup w) with
  | (true, some adv) =>
    let origin := if lean3Words.contains w then "Lean 3" else "Rocq/Coq"
    some s!"`{w}` is {origin}, not Lean 4 — {adv}."
  | _ =>
  if (trimStr sentence).endsWith "." && (kind == "syntax" || head.contains "field notation") then
    some "Lean 4 tactics do not end with a period — drop the trailing `.` (one tactic per line)."
  else if msg.contains "maximum number of heartbeats" || head.contains "(deterministic) timeout" then
    some "this tactic is too slow here (Lean's heartbeat budget ran out) — try a different approach: `omega`/`simp`/`norm_num` instead of `decide`, `intro` first, or split the problem with `have`."
  else if head.contains "unknown tactic" then
    match available with
    | some avail =>
      match avail.lookup w with
      | some false =>
        some s!"`{w}` is not available with this file's imports (it exists in Mathlib — add `import Mathlib.Tactic` or `import Mathlib` to the file)."
      | _ =>
        some "unknown tactic: check the spelling; Lean 4 tactic names are lowercase (`omega`, `simp`, `linarith`, `nlinarith`, `norm_num`, `ring`, `decide`, `aesop`, `exact?`)."
    | none =>
      some "unknown tactic: check the spelling; Lean 4 tactic names are lowercase (`omega`, `simp`, `linarith`, `nlinarith`, `norm_num`, `ring`, `decide`, `aesop`, `exact?`)."
  else if head.contains "unexpected token ','" || head.contains "unexpected token 'with'" then
    some "this is usually Lean 3 syntax. Lean 4: `fun x => e` (not `λ x, e`), `obtain ⟨a, b⟩ := h` (not `cases h with a b`), `rw [h]` (not `rw h`), `induction n with | zero => .. | succ n ih => ..`."
  else if head.contains "unexpected token '{'" then
    some "Lean 4 focuses goals with `·` (or `case tag => ...`), not `{ }`."
  else if head.startsWith "unexpected token" && head.contains "expected" then
    some "Lean 4 syntax: `rw [h]` with brackets, `fun x => e`, `⟨a, b⟩` anonymous constructors, `h.1`/`h.2` projections, `←` for reverse rewriting."
  else if msg.contains "linarith failed" then
    some "`linarith` is linear only: give it products as hints (`nlinarith [sq_nonneg (a - b), mul_pos ha hb]`), prove a helper `have` first, or use `positivity` for `0 ≤ _`/`0 < _` goals."
  else if msg.contains "nlinarith failed" || (msg.contains "failed to find a contradiction" && sentence.contains "nlinarith") then
    some "add the auxiliary facts nlinarith needs as hints: `nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy, sq_abs x]`."
  else if msg.contains "omega could not prove" || (head.contains "omega" && head.contains "failed") then
    some "`omega` handles linear ℕ/ℤ arithmetic only (no multiplication of variables, no ℝ) — for ℝ/ℚ use `linarith`/`nlinarith`; for nonlinear ℕ try `nlinarith` or `Nat.le_antisymm`-style lemmas."
  else if head.contains "made no progress" then
    some "the goal is not changed by this simp set — try `simp only [lemma]`, `norm_num`, `ring_nf`, `omega`, or `decide`."
  else if head.contains "motive is not type correct" then
    some "`rw` cannot rewrite under a dependent type here — try `simp only [h]`, `conv`, or rewrite in a `have` first."
  else if head.startsWith "The rfl tactic failed" || (head.contains "rfl" && head.contains "failed") then
    some "the two sides are not definitionally equal — try `simp`, `norm_num`, `ring`, `decide`, or `omega`."
  else if head.contains "No goals to be solved" || head.contains "no goals to be proved" then
    some "the proof was already complete before this tactic — remove it (call `state` to see the committed proof)."
  else if kind == "unknown_ref" then
    let name := (extractQuoted head.toList).getD ""
    if looksLikeCoqLemma name || coqPrefixes.any (fun p => name.startsWith p) then
      some "that looks like a Rocq/Coq lemma name; Mathlib names are snake_case with operator words (`mul_le_mul`, `sq_nonneg`, `add_pos`, `pow_le_pow_left`) — use `exact?` / `apply?` to find the real one."
    else
      some "unknown name — search with `exact?` / `apply?` / `rw?` as a step, or `#check Nat.` style queries; near-miss names may be listed below."
  else if head.contains "Type mismatch" || head.contains "type mismatch" then
    some "state the intermediate fact explicitly (`have h : <expected type> := by ...`) or use `exact?` to find a term of the expected type."
  else
    none

def withHint (body sentence msg kind : String) (available : Option (List (String × Bool)) := none) :
    String :=
  match hintFor sentence msg kind available with
  | some h => body ++ "\nhint: " ++ h
  | none => body

/-! ### hint-term synthesis (rung 9): auxiliary facts for nlinarith/positivity -/

/-- Facts computed from the current goal's local context and conclusion,
supplied by the Driver (phase 2b/3) via `MetaM`, not by scanning a printed
goal string. -/
structure GoalFacts where
  arithVars : List String
  posHyps : List (String × String)
  evenPowers : List (String × Nat)
  deriving Inhabited

private def pairsOf (xs : List String) : List String :=
  match xs with
  | [] => []
  | x :: rest =>
    (rest.flatMap (fun y => [s!"sq_nonneg ({x} - {y})", s!"sq_nonneg ({x} + {y})", s!"mul_self_nonneg ({x} * {y})"]))
      ++ pairsOf rest

private def prodsOf (xs : List (String × String)) : List String :=
  match xs with
  | [] => []
  | (h1, _) :: rest => (rest.map (fun (h2, _) => s!"mul_pos {h1} {h2}")) ++ prodsOf rest

/-- Verbatim port of `synth_candidates`, minus the goal-string scanning
(`arith_vars`/`positivity_hyps`/the regex half of `power_terms`), which the
Driver performs against `MetaM` and passes in as `GoalFacts`. Empty when
`enabled` is `false` (the caller reads `LEAN_AUTO2` via `auto2On` itself). -/
def synthCandidates (f : GoalFacts) (enabled : Bool) : List String :=
  if !enabled then []
  else
    let vars := f.arithVars
    let rawExtra := f.evenPowers.flatMap (fun be =>
      let (b, p) := be
      if p >= 2 && p % 2 == 0 then
        let h := p / 2
        let base := if h > 1 then s!"{b} ^ {h}" else b
        [s!"{base} - 1", s!"{base} + 1"]
      else [])
    let extra := (dedupe rawExtra).take 4
    let pos := f.posHyps
    let facts := vars.map (fun v => s!"sq_nonneg ({v})") ++ extra.map (fun t => s!"sq_nonneg ({t})")
    let pairs := pairsOf vars
    let prods := prodsOf pos
    if facts.isEmpty && pairs.isEmpty && prods.isEmpty then []
    else
      let sep := ", "
      let allFacts := facts ++ pairs ++ prods
      let c1 := [s!"nlinarith [{sep.intercalate (allFacts.take 10)}]"]
      let c2 := if pairs.isEmpty then [] else [s!"nlinarith [{sep.intercalate (pairs.take 6)}]"]
      let c3 := if extra.isEmpty then [] else
        [s!"nlinarith [{sep.intercalate (extra.map (fun t => s!"sq_nonneg ({t})"))}]"]
      let c4 := if prods.isEmpty then [] else
        [s!"nlinarith [{sep.intercalate prods}]", "positivity"]
      (c1 ++ c2 ++ c3 ++ c4).take 8

end LeanMcpEvolve.Hints
