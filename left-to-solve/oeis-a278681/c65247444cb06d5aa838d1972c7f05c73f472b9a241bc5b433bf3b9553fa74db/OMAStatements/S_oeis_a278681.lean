import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The recurrence and generating function for OEIS A278681

Source: https://oeis.org/A278681/internal
The floor in the defining sequence is natural-number division. The stated
linear recurrence and ordinary generating function use integer coefficients.
-/

namespace OMA.S_oeis_a278681

def a : ℕ → ℕ
  | 0 => 3
  | 1 => 16
  | n + 2 => a (n + 1) ^ 2 / a n

open PowerSeries

theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 4 * (a (n - 2) : ℤ) +
      2 * (a (n - 3) : ℤ) - 2 * (a (n - 4) : ℤ)) ∧
    ((1 - 6 * X + 4 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4) *
      PowerSeries.mk (fun n => (a n : ℤ)) = 3 - 2 * X + X ^ 2 - X ^ 3) := by
  sorry

end OMA.S_oeis_a278681
