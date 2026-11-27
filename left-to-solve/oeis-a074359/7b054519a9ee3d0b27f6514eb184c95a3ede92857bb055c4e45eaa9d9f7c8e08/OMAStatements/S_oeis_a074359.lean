import Mathlib

/-!
# The coefficient of q² in the polynomial sequence of OEIS A074359

Source: https://oeis.org/A074359
The polynomial indeterminate represents q. The power series indeterminate represents x.
-/

namespace OMA.S_oeis_a074359

open Polynomial

noncomputable def nu (b w : ℤ) : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => C b
  | n + 2 => C b * nu b w (n+1) + C w * (∑ i ∈ Finset.range (n+1), X^i) * nu b w n

noncomputable def a (n : ℕ) : ℤ := (nu 2 2 n).coeff 2

theorem main :
    let x := (PowerSeries.X : PowerSeries ℤ)
    (2 * x^2 + 2 * x - 1)^3 * PowerSeries.mk a =
      4 * x^4 * (-3 + 2*x + 8*x^2 + 4*x^3) := by
  sorry

end OMA.S_oeis_a074359
