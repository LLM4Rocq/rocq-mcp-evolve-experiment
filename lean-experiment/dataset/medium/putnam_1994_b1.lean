import Mathlib

open Filter Topology

-- {n : ℤ | (315 ≤ n ∧ n ≤ 325) ∨ (332 ≤ n ∧ n ≤ 350)}
/--
Find all positive integers $n$ that are within $250$ of exactly $15$ perfect squares.
-/
theorem putnam_1994_b1
    (n : ℤ) :
    n ∈ (({n : ℤ | (315 ≤ n ∧ n ≤ 325) ∨ (332 ≤ n ∧ n ≤ 350)}) : Set ℤ ) ↔
    (0 < n ∧ {m : ℕ | |n - m ^ 2| ≤ 250}.encard = 15) :=
  sorry
