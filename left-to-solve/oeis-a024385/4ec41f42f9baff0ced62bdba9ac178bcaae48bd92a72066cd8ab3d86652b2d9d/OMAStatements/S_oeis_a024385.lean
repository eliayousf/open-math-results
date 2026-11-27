import Mathlib.Data.Int.DivMod
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Mathar's recurrence and generating function for A024385

Source: https://oeis.org/A024385
The recurrence starts at index nine because the source offset is one.
The ordinary generating function has zero constant coefficient.
-/

namespace OMA.S_oeis_a024385

/-- The first and second elementary symmetric sums of the first m positive
integers congruent to 1 modulo 4. -/
def stats : ℕ → ℤ × ℤ
  | 0 => (0,0)
  | n+1 => ((stats n).1 + (4 * (n : ℤ) + 1),
             (stats n).2 + (4 * (n : ℤ) + 1) * (stats n).1)

/-- The floor of the source ratio, with a zero constant coefficient. -/
def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else (stats (n+1)).2 / (stats (n+1)).1

open PowerSeries in
theorem main :
    (∀ n ≥ 9, a n = 2*a (n-1) - a (n-2) + a (n-6) - 2*a (n-7) + a (n-8)) ∧
    ((1-X)^2*(1-X^6) * mk a = 3*X^2+3*X^3+X^4+2*X^5+2*X^6+2*X^7-X^8) := by
  sorry

end OMA.S_oeis_a024385
