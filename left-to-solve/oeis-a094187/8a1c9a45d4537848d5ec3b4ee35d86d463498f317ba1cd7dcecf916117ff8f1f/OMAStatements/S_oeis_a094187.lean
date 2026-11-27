import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Cast.Order

/-!
# Mathar's recurrence for A094187

Source: https://oeis.org/A094187
The source's denominator and programs use a prescribed integer scale.
The exact rational finite sum integrates the binomial expansion term by term.
-/

namespace OMA.S_oeis_a094187

open Finset

/-- Integral of x to the power -2k from 1 to 9/8, obtained by evaluating
its elementary antiderivative. -/
def moment (k : ℕ) : ℚ :=
  ((9 / 8 : ℚ) * (64 / 81 : ℚ)^k - 1) / (1 - 2 * (k : ℚ))

/-- Integrate the binomial expansion of (1-x^(-2))^n term by term. -/
def integral (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (-1 : ℚ)^k * moment k

/-- Product of the positive odd integers through 2n−1. -/
def oddprod (n : ℕ) : ℚ :=
  ∏ k ∈ range n, (2 * (k : ℚ) + 1)

/-- The source integral multiplied by its stated denominator
8 times 9^(2n−1) times the odd product. -/
def a (n : ℕ) : ℚ :=
  (8 / 9 : ℚ) * 81 ^ n * oddprod n * integral n

theorem main : ∀ n ≥ 3,
    a n = (196 * (n : ℚ) - 51) * a (n - 1) -
      2754 * ((n : ℚ) - 1) * (2 * (n : ℚ) - 3) * a (n - 2) := by
  sorry

end OMA.S_oeis_a094187
