import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Barker's closed form and generating function for A067016

Source: https://oeis.org/A067016
The closed form is multiplied by two to avoid an integer quotient.
-/

namespace OMA.S_oeis_a067016

open Finset

def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | k + 4 => univ.sup (fun i : Fin (k + 4) => a i + a (k + 3 - i))
termination_by n
decreasing_by
  all_goals have hi := i.isLt; omega

open PowerSeries in
theorem main :
    (∀ n ≥ 4, 2 * (a n : ℤ) = -3 + (-1 : ℤ)^n + 4*(n : ℤ)) ∧
    ((1-X)^2 * (1+X) * mk (fun n => (a n : ℤ)) =
      1 + 3*X - 2*X^2 - 4*X^3 + 6*X^4 + 2*X^5 - 2*X^6) := by
  sorry

end OMA.S_oeis_a067016
