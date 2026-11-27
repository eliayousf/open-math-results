import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The recurrence and generating function of OEIS A203235

Source: https://oeis.org/A203235
The zero term is adjoined for the ordinary generating function.
The recurrence starts at the first index with all positive-indexed terms.
-/

namespace OMA.S_oeis_a203235

open PowerSeries

/-- The repeating sequence in the OEIS definition, indexed from zero. -/
def digit (n : ℕ) : ℤ :=
  match n % 4 with
  | 0 => 1
  | 1 => 1
  | 2 => 1
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
    (∀ n : ℕ, 8 < n → a n = 6 * a (n-4) - 9 * a (n-8)) ∧
    ((1 - C 3 * X^4 : ℤ⟦X⟧)^2 * mk a = X^1 + C 2 * X^2 + C 3 * X^3 + C 10 * X^4 + C 7 * X^5 + C 4 * X^6 + X^7) := by
  sorry

end OMA.S_oeis_a203235
