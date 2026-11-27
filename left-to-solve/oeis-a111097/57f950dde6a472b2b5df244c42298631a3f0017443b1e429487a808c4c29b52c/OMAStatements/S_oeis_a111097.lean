import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Urn-size maximum likelihood for OEIS A111097

Source: https://oeis.org/A111097

The observation is that independent uniform draws with replacement produce
`n` distinct marbles and then repeat a marble. For an urn of size `N`, its
likelihood is `n * N.descFactorial n / N^(n+1)`. The sequence selects the
least positive size that maximizes this likelihood. The series starts at
index 1, with coefficient 0 at index 0.
-/

namespace OMA.S_oeis_a111097

def likelihood (n N : ℕ) : ℚ :=
  (n : ℚ) * (N.descFactorial n : ℚ) / (N : ℚ) ^ (n + 1)

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    sInf {N : ℕ | 0 < N ∧ ∀ K : ℕ, 0 < K → likelihood n K ≤ likelihood n N}

def secondDifferenceValue (n : ℕ) : ℤ :=
  if n = 1 then 2 else if n % 3 = 0 then 2 else if n % 3 = 1 then 1 else 0

open PowerSeries in
theorem main :
    (a 1 = 1) ∧
    (∀ n : ℕ, 2 ≤ n → a n = n * (n + 1) / 2 - 1 - (n - 1) / 3) ∧
    (∀ n : ℕ, 0 < n →
      (a (n + 2) : ℤ) - 2 * (a (n + 1) : ℤ) + (a n : ℤ) = secondDifferenceValue n) ∧
    ((1 - X) ^ 3 * (1 + X + X ^ 2) * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (1 + 2 * X ^ 2 - X ^ 3 + 2 * X ^ 4 - X ^ 5)) := by
  sorry

end OMA.S_oeis_a111097
