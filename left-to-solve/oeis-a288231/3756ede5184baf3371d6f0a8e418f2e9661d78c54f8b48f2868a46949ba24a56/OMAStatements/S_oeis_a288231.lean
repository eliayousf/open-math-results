import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.RingTheory.PowerSeries.Inverse

-- Formalization by Herman Palmgren (@PalmtreeBranch), using Codex.
-- Source: https://oeis.org/A288231

/-! The conjecture of Clark Kimberling on the reciprocal series for the real cube root of 4,
OEIS A288231, 10 July 2017. -/

namespace OMA.S_oeis_a288231

noncomputable def weight (r : ℝ) (n : ℕ) : ℚ := (⌊((n : ℝ) + 1) * r⌋ : ℤ)

/-- The coefficient of x^j in the denominator is (-1)^j times floor((j+1)r). -/
noncomputable def denominator (r : ℝ) : PowerSeries ℚ :=
  PowerSeries.mk fun j => (-1 : ℚ) ^ j * weight r j

noncomputable def a (r : ℝ) (n : ℕ) : ℚ := PowerSeries.coeff n (denominator r)⁻¹

theorem main : StrictMono (a ((4 : ℝ) ^ (1 / 3 : ℝ))) := by
  sorry

end OMA.S_oeis_a288231
