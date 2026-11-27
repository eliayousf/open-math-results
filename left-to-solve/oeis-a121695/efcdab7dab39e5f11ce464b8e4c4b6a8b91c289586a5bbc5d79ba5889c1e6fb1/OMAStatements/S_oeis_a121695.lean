import Mathlib.Data.Nat.Factorial.Basic

/-!
# Mathar's recurrence for A121695

Source: https://oeis.org/A121695
The source offset is one. The recurrence starts at index 5.
-/

namespace OMA.S_oeis_a121695

/-- OEIS A121696, using its published recurrence at positive indices. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => a (n + 1) + ((n : ℤ) + 3) * (n + 1).factorial * ↑((n + 2) / 2)

/-- OEIS A121695, the complement of A121696 among the `n!` deco polyominoes. -/
def b (n : ℕ) : ℤ := (n.factorial : ℤ) - a n

theorem main : ∀ n : ℕ, 5 ≤ n →
    b n + b (n - 1) - (n : ℤ) * ((n : ℤ) - 2) * b (n - 2) -
      (2 * (n : ℤ) - 3) * ((n : ℤ) - 2) * b (n - 3) -
      ((n : ℤ) - 2) * ((n : ℤ) - 3) * b (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a121695
