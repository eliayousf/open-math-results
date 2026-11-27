import Mathlib

/-!
# OEIS A074358: the coefficient of q in the polynomial sequence nu

Source: https://oeis.org/A074358
Here q is the polynomial indeterminate and x is the generating series variable.
-/

namespace OMA.S_oeis_a074358

open Polynomial

noncomputable def nu : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * nu (n + 1) + 2 * (∑ i ∈ Finset.range (n + 1), X ^ i) * nu n

noncomputable def a (n : ℕ) : ℤ := (nu n).coeff 1

open scoped PowerSeries

noncomputable def closed (n : ℕ) : ℝ :=
  let s := Real.sqrt 3
  ((1 + s)^n * (-9 + 2*s) - (1 - s)^n * (9 + 2*s) +
      3 * ((1 - s)^n + (1 + s)^n) * n) / 18

theorem main :
    (let x := (PowerSeries.X : PowerSeries ℤ)
     (2*x^2 + 2*x - 1)^2 * PowerSeries.mk a = 4*x^3*(x+1)) ∧
    (∀ n : ℕ, 0 < n → (a n : ℝ) = closed n) ∧
    (∀ n : ℕ, 4 < n → a n = 4*a (n-1) - 8*a (n-3) - 4*a (n-4)) := by
  sorry

end OMA.S_oeis_a074358
