import Mathlib

/-!
# OEIS A074360: the coefficient of q³ in the polynomial sequence nu

Source: https://oeis.org/A074360
The polynomial indeterminate represents q. The power series indeterminate represents x.
-/

namespace OMA.S_oeis_a074360

open Polynomial

noncomputable def nu : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * nu (n + 1) + 2 * (∑ i ∈ Finset.range (n + 1), X ^ i) * nu n

noncomputable def a (n : ℕ) : ℤ := (nu n).coeff 3

theorem main :
    let x := (PowerSeries.X : PowerSeries ℤ)
    (2*x^2 + 2*x - 1)^4 * PowerSeries.mk a =
      8*x^5*(1+x)*(12*x^4 + 24*x^3 - 2*x^2 - 16*x + 5) := by
  sorry

end OMA.S_oeis_a074360
