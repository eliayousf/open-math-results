import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The recurrence and generating function of OEIS A203166

Source: https://oeis.org/A203166
The zero term is adjoined for the ordinary generating function.
The recurrence starts at the first index with all positive-indexed terms.
-/

namespace OMA.S_oeis_a203166

open PowerSeries

/-- The repeating sequence in the OEIS definition, indexed from zero. -/
def digit (n : ℕ) : ℤ :=
  match n % 5 with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | _ => 5

/-- The full product and the sum of the products omitting one factor. -/
def products : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (p, e) := products n
    (p * digit n, e * digit n + p)

/-- The elementary symmetric function of degree n−1, extended by zero at n=0. -/
def a (n : ℕ) : ℤ := (products n).2

theorem main :
    (∀ n : ℕ, 10 < n → a n = 240 * a (n-5) - 14400 * a (n-10)) ∧
    ((1 - C 120 * X^5 : ℤ⟦X⟧)^2 * mk a = X^1 + C 3 * X^2 + C 11 * X^3 + C 50 * X^4 + C 274 * X^5 + C 154 * X^6 + C 188 * X^7 + C 324 * X^8 + C 576 * X^9) := by
  sorry

end OMA.S_oeis_a203166
