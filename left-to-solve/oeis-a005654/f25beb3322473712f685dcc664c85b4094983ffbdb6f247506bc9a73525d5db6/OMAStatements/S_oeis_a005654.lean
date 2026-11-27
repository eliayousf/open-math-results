import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs

/-! Mathar's recurrence for the A005654 bracelet counts.

The author omits the lower index. All five terms lie in the source domain for
n at least five. Michael Somos's published binomial count specifies the series.
Source: https://oeis.org/A005654/internal
-/

namespace OMA.S_oeis_a005654

/-- The established bracelet count formula published in OEIS A005654. -/
def a (n : ℕ) : ℚ :=
  ((Nat.choose (2 * n - 1) n : ℚ) + (Nat.choose (n - 1) (n / 2) : ℚ)) / 2

/-- The integer-coefficient operator in Mathar's recurrence. -/
def residual (f : ℕ → ℚ) (n : ℕ) : ℚ :=
  let z : ℚ := n
  z * (z - 2) * f n - (5 * z - 3) * (z - 2) * f (n - 1) +
    4 * (z - 2) * f (n - 2) + 4 * (5 * z ^ 2 - 27 * z + 37) * f (n - 3) -
    8 * (2 * z - 7) * (z - 4) * f (n - 4)

theorem main : ∀ n : ℕ, 5 ≤ n → residual a n = 0 := by
  sorry

end OMA.S_oeis_a005654
