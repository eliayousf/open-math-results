import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Generating function of OEIS A023861

Source: https://oeis.org/A023861
Maksym Voznyy's July 2009 conjecture is stated after clearing the denominator
and changing the common sign of numerator and denominator.
-/

namespace OMA.S_oeis_a023861

open PowerSeries

/-- The Lucas numbers, indexed from zero. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

def weightedSum (n m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range m, (k + 1 : ℕ) * lucas (n - k)

/-- The weighted sum in the OEIS definition. The index `k` starts at zero. -/
def a (n : ℕ) : ℤ := weightedSum n ((n + 1) / 2)

theorem main : ((1-X-X^2 : ℤ⟦X⟧) * (1-X^2-X^4)^2) * mk a =
    X + C 2 * X^2 + C 4 * X^3 - C 2 * X^4 - X^5 + C 3 * X^6 := by
  sorry

end OMA.S_oeis_a023861
