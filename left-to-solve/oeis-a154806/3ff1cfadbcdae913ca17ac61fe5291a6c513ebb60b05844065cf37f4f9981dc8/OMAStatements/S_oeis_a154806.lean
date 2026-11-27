import Mathlib.Data.Nat.Digits.Defs
import Mathlib.RingTheory.PowerSeries.Basic

/-! Closed form and generating function for the binary run-length numbers.
Source: https://oeis.org/A154806/internal
For positive n there is one binary word with n runs of the fixed length:
its leading run is all ones, and subsequent runs alternate.
The constant coefficient of the series is zero. -/

namespace OMA.S_oeis_a154806

/-- Least significant first, with a block of w identical bits appended at each step. -/
def digits (w : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => List.replicate w (if n % 2 = 0 then 1 else 0) ++ digits w n

/-- The value of the unique positive word with n successive runs of length w. -/
def a (w n : ℕ) : ℤ := (Nat.ofDigits (2 : ℕ) (digits w n) : ℕ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 ≤ n → 34*a 4 n = 2*(2:ℤ)^(4*n+4)-15*(-1:ℤ)^n-17) ∧
    ((1-X^2)*(1-C (16:ℤ)*X)*mk (a 4)=C 15*X^1) := by
  sorry

end OMA.S_oeis_a154806
