import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Mathar's recurrence for A191792

Source: https://oeis.org/A191792
The recurrence starts at index 8, so all indices are nonnegative.
-/

namespace OMA.S_oeis_a191792

open PowerSeries

noncomputable def K : PowerSeries ℚ := 1 - 2 * X + X ^ 2 - 2 * X ^ 3 + X ^ 4
noncomputable def T : PowerSeries ℚ := 1 + 2 * X + X ^ 2 + 2 * X ^ 3 + X ^ 4

noncomputable def radical : PowerSeries ℚ := PowerSeries.subst
  (-(2 * X ^ 2) - 5 * X ^ 4 - 2 * X ^ 6 + X ^ 8 : PowerSeries ℚ)
  (binomialSeries ℚ (1 / 2 : ℚ))

noncomputable def B : PowerSeries ℚ := radical * K⁻¹

/-- The source quadratic generating function, with its constant-term-one branch. -/
noncomputable def a (n : ℕ) : ℚ := coeff (n + 1) (B - 1) / 2

theorem main : ∀ n : ℕ, 8 ≤ n →
    ((n : ℚ) + 1) * a n - 2 * a (n - 1) + 2 * (-(n : ℚ) + 1) * a (n - 2) -
      4 * a (n - 3) + 5 * (-(n : ℚ) + 3) * a (n - 4) + 4 * a (n - 5) +
      2 * (-(n : ℚ) + 5) * a (n - 6) + 2 * a (n - 7) + ((n : ℚ) - 7) * a (n - 8) = 0 := by
  sorry

end OMA.S_oeis_a191792
