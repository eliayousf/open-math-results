import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The conjectured OEIS formula for A203230

Source: https://oeis.org/A203230
The sequence starts at index one, and its value at zero is adjoined.
The recurrence starts at the first index with all positive-indexed terms.
-/

namespace OMA.S_oeis_a203230

open PowerSeries

/-- The repeating sequence in the OEIS definition, indexed from zero. -/
def digit (n : ℕ) : ℤ :=
  match n % 2 with
  | 0 => 1
  | _ => 3

/-- The full product and the sum of the products omitting one factor. -/
def products : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (p, e) := products n
    (p * digit n, e * digit n + p)

/-- The elementary symmetric function of degree n−1, extended by zero at n=0. -/
def a (n : ℕ) : ℤ := (products n).2

theorem main :
    (∀ n : ℕ, 4 < n → a n = 6 * a (n-2) - 9 * a (n-4)) ∧
    ((1 - C 3 * X^2 : ℤ⟦X⟧)^2 * mk a = X^1 + C 4 * X^2 + X^3) := by
  sorry

end OMA.S_oeis_a203230
