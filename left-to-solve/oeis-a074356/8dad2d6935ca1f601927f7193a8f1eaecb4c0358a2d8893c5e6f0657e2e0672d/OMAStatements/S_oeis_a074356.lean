import Mathlib

/-!
# The coefficient of q² in the polynomial sequence of OEIS A074356

Source: https://oeis.org/A074356
The polynomial indeterminate represents q. The power series indeterminate represents x.
-/

namespace OMA.S_oeis_a074356

open Polynomial

noncomputable def nu (b w : ℤ) : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => C b
  | n + 2 => C b * nu b w (n+1) + C w * (∑ i ∈ Finset.range (n+1), X^i) * nu b w n

noncomputable def a (n : ℕ) : ℤ := (nu 1 3 n).coeff 2

theorem main :
    (let x := (PowerSeries.X : PowerSeries ℤ)
     (1-x-3*x^2)^3 * PowerSeries.mk a = 3*x^4*(2-3*x)*(2+4*x+3*x^2)) ∧
    (∀ n : ℕ, 7 < n → a n =
      3*a (n-1) + 6*a (n-2) - 17*a (n-3) - 18*a (n-4) + 27*a (n-5) + 27*a (n-6)) := by
  sorry

end OMA.S_oeis_a074356
