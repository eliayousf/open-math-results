import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Mathar's recurrence for A351933

Source: https://oeis.org/A351933
The recurrence starts at index four, so all indices are nonnegative.
-/

namespace OMA.S_oeis_a351933

open PowerSeries

noncomputable def denominator : PowerSeries ℚ := 2 - X ^ 2

/-- The formal series for `X / (1 - X²/2)`. -/
noncomputable def argument : PowerSeries ℚ := 2 * X * denominator⁻¹

/-- The exponential generating series of A351933. -/
noncomputable def series : PowerSeries ℚ := (PowerSeries.exp ℚ).subst argument

/-- The factorial-scaled coefficients of the defining exponential generating series. -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n series

theorem main : ∀ n : ℕ, 4 ≤ n →
    4 * a n - 4 * a (n - 1) - 4 * ((n : ℚ) - 1) * ((n : ℚ) - 2) * a (n - 2) -
      2 * ((n : ℚ) - 1) * ((n : ℚ) - 2) * a (n - 3) +
      ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a351933
