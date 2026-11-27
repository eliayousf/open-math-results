import Mathlib.Data.Nat.Factorial.Basic

/-!
# Mathar's recurrence for A121696

Source: https://oeis.org/A121696
The source offset is one. The recurrence starts at index 4.
-/

namespace OMA.S_oeis_a121696

/-- OEIS A121696, using its published recurrence at positive indices. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => a (n + 1) + ((n : ℤ) + 3) * (n + 1).factorial * ↑((n + 2) / 2)

theorem main : ∀ n : ℕ, 4 ≤ n →
    a n - ((n : ℤ) - 1) ^ 2 * a (n - 2) - (n : ℤ) * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a121696
