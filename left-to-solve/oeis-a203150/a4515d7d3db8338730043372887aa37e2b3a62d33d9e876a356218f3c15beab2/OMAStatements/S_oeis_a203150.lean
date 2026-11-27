import Mathlib.Analysis.Real.Sqrt

/-!
# The conjectured OEIS formula for A203150

Source: https://oeis.org/A203150
The published square-root expression is retained verbatim in meaning.
Indices of the sequence start at one.
-/

namespace OMA.S_oeis_a203150

/-- The alternating entries 1 and 2, indexed from zero. -/
def digit (n : ℕ) : ℤ := if n % 2 = 0 then 1 else 2

/-- The full product and the sum of the products obtained by omitting one factor. -/
def products : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (p, e) := products n
    (p * digit n, e * digit n + p)

def a (n : ℕ) : ℤ := (products n).2

theorem main : ∀ n : ℕ, 0 < n →
    let r := Real.sqrt 2
    (a n : ℝ) =
      (6 * r * (n : ℝ) + (1 + 3 * (1-r) * (n : ℝ)) * (1 - (-1 : ℝ)^n)) *
        r^(n-1) / 8 := by
  sorry

end OMA.S_oeis_a203150
