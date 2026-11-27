import Mathlib.NumberTheory.BernoulliPolynomials

/-! Cubefreeness of the denominators in OEIS A363151. Source: https://oeis.org/A363151/internal -/

namespace OMA.S_oeis_a363151

open Finset

/-- The denominator of the convolution of Bernoulli polynomials evaluated at one. -/
noncomputable def a (n : ℕ) : ℕ :=
  (∑ j ∈ range (n + 1), (Polynomial.bernoulli j).eval 1 *
    (Polynomial.bernoulli (n - j)).eval 1).den

theorem main : ∀ n r : ℕ, Nat.Prime r → ¬ r ^ 3 ∣ a n := by
  sorry

end OMA.S_oeis_a363151
