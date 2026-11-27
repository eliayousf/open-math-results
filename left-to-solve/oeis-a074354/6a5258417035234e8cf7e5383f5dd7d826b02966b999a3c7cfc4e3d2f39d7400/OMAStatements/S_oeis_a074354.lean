import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The coefficient of q³ in the polynomial sequence of OEIS A074354

Source: https://oeis.org/A074354
The polynomial indeterminate represents q. The power series indeterminate represents x.
-/

namespace OMA.S_oeis_a074354

open Polynomial

noncomputable def nu (b w : ℤ) : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => C b
  | n + 2 => C b * nu b w (n+1) + C w * (∑ i ∈ Finset.range (n+1), X^i) * nu b w n

noncomputable def a (n : ℕ) : ℤ := (nu 1 2 n).coeff 3

theorem main :
    (let x := (PowerSeries.X : PowerSeries ℤ)
     ((1+x)^4 * (1-2*x)^4) * PowerSeries.mk a =
       2*x^5*(1+2*x)*(7-10*x-13*x^2+12*x^3+12*x^4)) ∧
    (∀ n : ℕ, 10 < n → a n = 4*a (n-1) + 2*a (n-2) - 20*a (n-3) - a (n-4) +
      40*a (n-5) + 8*a (n-6) - 32*a (n-7) - 16*a (n-8)) := by
  sorry

end OMA.S_oeis_a074354
