import Mathlib.Data.Int.Basic

/-!
# The conjectured OEIS formula for A203157

Source: https://oeis.org/A203157
The sequence starts at index one, and its value at zero is adjoined.
The recurrence starts at the first index with all positive-indexed terms.
-/

namespace OMA.S_oeis_a203157

/-- Triangular numbers indexed with the usual zero at index zero. -/
def tri : ℕ → ℤ
  | 0 => 0
  | n + 1 => tri n + (n : ℤ) + 1

/-- The full product and the omission sum for the first n positive triangular numbers. -/
def products : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (p, e) := products n
    let t := tri (n + 1)
    (p * t, e * t + p)

def a (n : ℕ) : ℤ := (products n).2

theorem main : ∀ n : ℕ, 1 < n →
    2 * (-(n : ℤ) + 1) * a n + (n : ℤ)^3 * a (n - 1) = 0 := by
  sorry

end OMA.S_oeis_a203157
