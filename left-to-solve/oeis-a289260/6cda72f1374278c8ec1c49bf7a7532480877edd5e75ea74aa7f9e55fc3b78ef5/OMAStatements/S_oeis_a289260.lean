import Mathlib.RingTheory.PowerSeries.Inverse

/-!
Source: https://oeis.org/A289260, conjecture of Clark Kimberling.
OEIS Foundation, CC BY-SA 4.0.
-/

namespace OMA.S_oeis_a289260

open PowerSeries
open scoped PowerSeries

/-- The coefficient of X^n in the signed floor series with r = 8/5.
Natural division gives the floor because all arguments of the floor are positive. -/
def signedFloor (n : ℕ) : ℤ := (-1)^n * (↑(8 * (n + 1) / 5) : ℤ)

def denominator : ℤ⟦X⟧ := PowerSeries.mk signedFloor

/-- The denominator has constant coefficient 1, so it is inverted using the unit 1. -/
noncomputable def generatingSeries : ℤ⟦X⟧ := invOfUnit denominator 1

noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

theorem main : StrictMono a := by
  sorry

end OMA.S_oeis_a289260
