import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Generating function of OEIS A024459

Source: https://oeis.org/A024459
R. J. Mathar's April 2020 conjecture is stated after clearing the denominator
and changing the common sign of numerator and denominator.
-/

namespace OMA.S_oeis_a024459

open PowerSeries

/-- The Lucas numbers, indexed from zero. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- The Fibonacci numbers, indexed from zero. -/
def fibonacci : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacci (n + 1) + fibonacci n

def weightedSum (n m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range m, fibonacci (k + 1) * lucas (n - k)

/-- The weighted sum in the OEIS definition. The index `k` starts at zero. -/
def a (n : ℕ) : ℤ := weightedSum n ((n + 1) / 2)

theorem main : ((1+X^2 : ℤ⟦X⟧) * (1+X-X^2) * (1-X-X^2)^2) * mk a =
    X + C 2 * X^2 + X^3 - C 3 * X^4 := by
  sorry

end OMA.S_oeis_a024459
