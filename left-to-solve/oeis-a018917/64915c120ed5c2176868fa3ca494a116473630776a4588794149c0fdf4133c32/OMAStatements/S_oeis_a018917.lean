import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Recurrence, generating function, and Padovan identity for OEIS A018917

Source: https://oeis.org/A018917/internal
The defining greatest integer is strictly below the quotient. For positive
integer numerator and denominator it is the quotient after subtracting
one from the numerator. The Padovan sequence uses the offset of A000931.
-/

namespace OMA.S_oeis_a018917

def a : ℕ → ℕ
  | 0 => 3
  | 1 => 5
  | n + 2 => (a (n + 1) ^ 2 - 1) / a n

def padovan : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | n + 3 => padovan (n + 1) + padovan n

open PowerSeries

theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = (a (n - 1) : ℤ) + (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧
    ((1 - X) * (1 - X ^ 2 - X ^ 3) * PowerSeries.mk (fun n => (a n : ℤ)) = 3 + 2 * X - X ^ 3) ∧
    (∀ n : ℕ, 0 < n → a n = a (n - 1) + padovan (n + 8)) := by
  sorry

end OMA.S_oeis_a018917
