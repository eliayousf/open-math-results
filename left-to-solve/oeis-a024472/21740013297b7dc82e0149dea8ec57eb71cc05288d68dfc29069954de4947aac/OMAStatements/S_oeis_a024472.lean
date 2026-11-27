import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Generating function of OEIS A024472

Source: https://oeis.org/A024472
R. J. Mathar's April 2020 conjecture is stated after clearing the denominator
and changing the common sign of numerator and denominator.
-/

namespace OMA.S_oeis_a024472

open PowerSeries

/-- The Lucas numbers, indexed from zero. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- The shifted Fibonacci numbers, with value F(n+1) at index n. -/
def shiftedFibonacci : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => shiftedFibonacci (n + 1) + shiftedFibonacci n

def weightedSum (n m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range m, lucas (k + 1) * shiftedFibonacci (n - k)

/-- The weighted sum in the OEIS definition. The index `k` starts at zero. -/
def a (n : ℕ) : ℤ := weightedSum n ((n + 1) / 2)

theorem main : ((1+X^2 : ℤ⟦X⟧) * (1+X-X^2) * (1-X-X^2)^2) * mk a =
    X + X^2 + C 4 * X^3 + X^4 - C 2 * X^5 := by
  sorry

end OMA.S_oeis_a024472
