import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Recurrence and generating function for OEIS A277088

Source: https://oeis.org/A277088/internal
The first stated rounding rule is the ceiling of the quotient. Arithmetic
on the positive numerator and denominator gives the natural division below.
-/

namespace OMA.S_oeis_a277088

def a : ℕ → ℕ
  | 0 => 5
  | 1 => 12
  | n + 2 => (a (n + 1) ^ 2 + a n - 1) / a n

open PowerSeries

theorem main :
    (∀ n : ℕ, 9 ≤ n → (a n : ℤ) =
      3 * (a (n - 1) : ℤ) - 2 * (a (n - 2) : ℤ) + 2 * (a (n - 3) : ℤ) -
        (a (n - 4) : ℤ) + (a (n - 6) : ℤ) - (a (n - 7) : ℤ) - (a (n - 9) : ℤ)) ∧
    ((1 - X) * (1 - 2 * X - 2 * X ^ 3 - X ^ 4 - X ^ 5 - 2 * X ^ 6 - X ^ 7 - X ^ 8) *
      PowerSeries.mk (fun n => (a n : ℤ)) =
        5 - 3 * X + 3 * X ^ 2 - 2 * X ^ 3 + X ^ 5 - 3 * X ^ 6 - X ^ 7 - 2 * X ^ 8) := by
  sorry

end OMA.S_oeis_a277088
