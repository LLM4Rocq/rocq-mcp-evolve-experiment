import Mathlib

-- 3
/--
What is the units (i.e., rightmost) digit of
\[
\left\lfloor \frac{10^{20000}}{10^{100}+3}\right\rfloor ?
\]
-/
theorem putnam_1986_a2
: (Nat.floor ((10 ^ 20000 : ℝ) / (10 ^ 100 + 3)) % 10 = ((3) : ℕ )) :=
sorry
