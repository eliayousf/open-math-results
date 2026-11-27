import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The recurrence and generating function for OEIS A278692

Source: https://oeis.org/A278692/internal
The floor in the defining sequence is natural-number division. The stated
linear recurrence and ordinary generating function use integer coefficients.
-/

namespace OMA.S_oeis_a278692

def a : ℕ → ℕ
  | 0 => 4
  | 1 => 14
  | n + 2 => a (n + 1) ^ 2 / a n

open PowerSeries

theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 4 * (a (n - 1) : ℤ) - 2 * (a (n - 2) : ℤ) +
      (a (n - 3) : ℤ) - (a (n - 4) : ℤ)) ∧
    ((1 - 4 * X + 2 * X ^ 2 - X ^ 3 + X ^ 4) *
      PowerSeries.mk (fun n => (a n : ℤ)) = 4 - 2 * X + X ^ 2 - X ^ 3) := by
  sorry

end OMA.S_oeis_a278692
