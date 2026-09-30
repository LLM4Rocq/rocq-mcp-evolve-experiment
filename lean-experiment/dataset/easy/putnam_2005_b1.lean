import Mathlib

open Nat Set

-- Note: There might be multiple possible correct answers.
-- (MvPolynomial.X 1 - 2 * MvPolynomial.X 0) * (MvPolynomial.X 1 - 2 * MvPolynomial.X 0 - 1)
/--
Find a nonzero polynomial $P(x,y)$ such that $P(\lfloor a \rfloor,\lfloor 2a \rfloor)=0$ for all real numbers $a$. (Note: $\lfloor \nu \rfloor$ is the greatest integer less than or equal to $\nu$.)
-/
theorem putnam_2005_b1
: ((MvPolynomial.X 1 - 2 * MvPolynomial.X 0) * (MvPolynomial.X 1 - 2 * MvPolynomial.X 0 - 1) : MvPolynomial (Fin 2) ℝ ) ≠ 0 ∧ ∀ a : ℝ, MvPolynomial.eval (fun n : Fin 2 => if (n = 0) then (Int.floor a : ℝ) else (Int.floor (2 * a))) ((MvPolynomial.X 1 - 2 * MvPolynomial.X 0) * (MvPolynomial.X 1 - 2 * MvPolynomial.X 0 - 1) : MvPolynomial (Fin 2) ℝ ) = 0 :=
sorry
