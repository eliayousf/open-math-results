import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Int.Basic

/-! Richard J. Mathar's November 2026 three-column polynomial for binary
matrices with at most two ones per row and column. The statement multiplies
by eight to use integer coefficients. The counting recursion chooses the
ones in each row subject to the remaining column capacities.
Source: https://oeis.org/A401159/internal
-/

namespace OMA.S_oeis_a401159

/-- Number of matrices with `n` labeled rows, `d` labeled columns of
capacity two, `s` other labeled columns of capacity one, and row capacity two.
At each step choose the one or two columns receiving a 1 in the first row.
A column whose capacity falls to zero has zeros in every remaining row. -/
def remaining : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 1
  | n + 1, d, s => remaining n d s
      + (d : ℤ) * remaining n (d - 1) (s + 1)
      + (s : ℤ) * remaining n d (s - 1)
      + (Nat.choose d 2 : ℤ) * remaining n (d - 2) (s + 2)
      + (d : ℤ) * (s : ℤ) * remaining n (d - 1) s
      + (Nat.choose s 2 : ℤ) * remaining n d (s - 2)

/-- Empty columns initially allow two entries per column. -/
def T (n m : ℕ) : ℤ := remaining n m 0

theorem main : ∀ n : ℕ,
    8 * T n 3 = 8 + 8*(n : ℤ) + 22*(n : ℤ)^2 + 13*(n : ℤ)^3
      + (n : ℤ)^4 + 3*(n : ℤ)^5 + (n : ℤ)^6 := by
  sorry

end OMA.S_oeis_a401159
