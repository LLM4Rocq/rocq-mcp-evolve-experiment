theorem b1 (n : Nat) : n + 1 = 1 + n := by
  bogus_tac

theorem b2 : True := by
  sorry

theorem b3 (n : Nat) : n + 0 = n := by
  rfl

/-- uses the broken b1 -/
theorem b4 (n : Nat) : 1 + n = n + 1 := by
  rw [b1]

theorem b5 : 2 = 3 := by
  decide
