import Mathlib.RingTheory.PowerSeries.Basic

/-! R. J. Mathar’s recurrence and generating function for OEIS A024220.
Source: https://oeis.org/A024220/internal
The OEIS offset is 1, so the first recurrence using seven earlier indexed terms is at 8.
The literal two-term set gives zero at index zero. The generating function is
stated after clearing the denominator and changing both polynomial signs. -/

namespace OMA.S_oeis_a024220

/-- The kth elementary symmetric function of the first m integers congruent to 1 modulo 3. -/
def e : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | m + 1, k + 1 => e m (k + 1) + (3 * (m : ℤ) + 1) * e m k

/-- The floor of the ratio in the source. The two-term set gives a zero at index zero. -/
def a (n : ℕ) : ℤ := e (n + 2) 3 / e (n + 2) 1

open PowerSeries in
theorem main :
    (∀ n : ℕ, 8 ≤ n → a n = 4 * a (n - 1) - 6 * a (n - 2) + 5 * a (n - 3) -
      5 * a (n - 4) + 6 * a (n - 5) - 4 * a (n - 6) + a (n - 7)) ∧
    ((1 - X) ^ 4 * (1 - X ^ 3) * mk a = 2 * X + 11 * X ^ 2 + 7 * X ^ 3 + 8 * X ^ 4 - X ^ 5) := by
  sorry

end OMA.S_oeis_a024220
