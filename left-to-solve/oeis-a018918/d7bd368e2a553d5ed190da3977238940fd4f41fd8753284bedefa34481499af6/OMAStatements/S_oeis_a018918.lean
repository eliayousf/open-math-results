import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Recurrence and generating function for OEIS A018918

Source: https://oeis.org/A018918/internal
The defining greatest integer is strictly below the quotient. For positive
integer numerator and denominator it is the quotient after subtracting
one from the numerator. The signs in the generating function are normalized.
-/

namespace OMA.S_oeis_a018918

def a : ℕ → ℕ
  | 0 => 3
  | 1 => 6
  | n + 2 => (a (n + 1) ^ 2 - 1) / a n

open PowerSeries

theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) +
      2 * (a (n - 3) : ℤ) - (a (n - 4) : ℤ)) ∧
    ((1 - X) * (1 - 2 * X + X ^ 2 - X ^ 3) *
      PowerSeries.mk (fun n => (a n : ℤ)) = 3 - 3 * X + 2 * X ^ 2 - X ^ 3) := by
  sorry

end OMA.S_oeis_a018918
