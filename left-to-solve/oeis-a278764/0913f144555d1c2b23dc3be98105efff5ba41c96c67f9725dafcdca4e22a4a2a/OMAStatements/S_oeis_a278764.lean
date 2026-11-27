import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The recurrence and generating function for OEIS A278764

Source: https://oeis.org/A278764/internal
The floor in the defining sequence is natural-number division. The stated
linear recurrence and ordinary generating function use integer coefficients.
-/

namespace OMA.S_oeis_a278764

def a : ℕ → ℕ
  | 0 => 5
  | 1 => 13
  | n + 2 => a (n + 1) ^ 2 / a n

open PowerSeries

theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 2 * (a (n - 2) : ℤ) +
      3 * (a (n - 3) : ℤ) - 3 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ) - (a (n - 6) : ℤ)) ∧
    ((1 - X) * (1 - 2 * X - 3 * X ^ 3 - X ^ 5) *
      PowerSeries.mk (fun n => (a n : ℤ)) = 5 - 2 * X + 4 * X ^ 2 - 5 * X ^ 3 + X ^ 4 - 2 * X ^ 5) := by
  sorry

end OMA.S_oeis_a278764
