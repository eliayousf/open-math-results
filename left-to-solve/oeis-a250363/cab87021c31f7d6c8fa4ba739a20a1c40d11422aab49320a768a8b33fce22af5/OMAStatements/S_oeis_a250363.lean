import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Generating function and recurrence for OEIS A250363

Source: https://oeis.org/A250363

Position i is indexed from zero. Its actual value is i plus its chosen offset
from 0 through n. This shifts the original values uniformly by one and
preserves repetitions. A value occurs at least four times precisely when
there is one position outside which all other values agree.
-/

namespace OMA.S_oeis_a250363

abbrev ArrayChoice (n : ℕ) := Fin 5 → Fin (n + 1)

def value {n : ℕ} (w : ArrayChoice n) (i : Fin 5) : ℕ := (w i).val + i.val

def equalOutside {n : ℕ} (w : ArrayChoice n) (i : Fin 5) : Prop :=
  ∀ j k : Fin 5, j ≠ i → k ≠ i → value w j = value w k

def bad {n : ℕ} (w : ArrayChoice n) : Prop := ∃ i : Fin 5, equalOutside w i

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.card { w : ArrayChoice n // ¬ bad w }

open PowerSeries in
theorem main :
    ((1 - X) ^ 6 * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (32 + 51 * X + 38 * X ^ 2 + 3 * X ^ 3 + 8 * X ^ 4 -
        29 * X ^ 5 + 22 * X ^ 6 - 5 * X ^ 7)) ∧
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
        15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a250363
