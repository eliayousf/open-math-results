import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Recurrence and generating function for OEIS A277089

Source: https://oeis.org/A277089/internal
The first stated rounding rule is the ceiling of the quotient. Arithmetic
on the positive numerator and denominator gives the natural division below.
-/

namespace OMA.S_oeis_a277089

def a : ℕ → ℕ
  | 0 => 6
  | 1 => 15
  | n + 2 => (a (n + 1) ^ 2 + a n - 1) / a n

open PowerSeries

theorem main :
    (∀ n : ℕ, 7 ≤ n → (a n : ℤ) =
      3 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ) - (a (n - 4) : ℤ) +
        2 * (a (n - 6) : ℤ) - 2 * (a (n - 7) : ℤ)) ∧
    ((1 - X) * (1 - 2 * X - X ^ 2 - X ^ 3 - 2 * X ^ 6) *
      PowerSeries.mk (fun n => (a n : ℤ)) =
        6 - 3 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 + 3 * X ^ 5 - 5 * X ^ 6) := by
  sorry

end OMA.S_oeis_a277089
