import Mathlib

/-!
# The coefficient of q³ in the polynomial sequence of OEIS A074357

Source: https://oeis.org/A074357
The polynomial indeterminate represents q. The power series indeterminate represents x.
-/

namespace OMA.S_oeis_a074357

open Polynomial

noncomputable def nu (b w : ℤ) : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => C b
  | n + 2 => C b * nu b w (n+1) + C w * (∑ i ∈ Finset.range (n+1), X^i) * nu b w n

noncomputable def a (n : ℕ) : ℤ := (nu 1 3 n).coeff 3

theorem main :
    let x := (PowerSeries.X : PowerSeries ℤ)
    (3*x^2+x-1)^4 * PowerSeries.mk a =
      3*x^5*(3*x+1)*(36*x^4+24*x^3-29*x^2-14*x+10) := by
  sorry

end OMA.S_oeis_a074357
