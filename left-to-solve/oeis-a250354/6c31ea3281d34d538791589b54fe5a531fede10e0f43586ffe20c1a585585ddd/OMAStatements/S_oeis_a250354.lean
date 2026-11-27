import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Fin

/-!
# Generating function and recurrence for OEIS A250354

Source: https://oeis.org/A250354

The zero-based position i has value i plus an offset from 0 through n.
Shifting all entries by one recovers the one-based intervals in the source
and preserves repetitions. The generating series begins at index one.
-/

namespace OMA.S_oeis_a250354

abbrev ArrayChoice (n : ℕ) := Fin 5 → Fin (n + 1)

def value {n : ℕ} (w : ArrayChoice n) (i : Fin 5) : ℕ := (w i).val + i.val

def positions {n : ℕ} (w : ArrayChoice n) (t : ℕ) : Finset (Fin 5) :=
  Finset.univ.filter fun i => value w i = t

def bad {n : ℕ} (w : ArrayChoice n) : Prop := ∃ t : ℕ, 3 ≤ (positions w t).card

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.card { w : ArrayChoice n // ¬ bad w }

open PowerSeries in
theorem main :
    ((1 - X) ^ 6 * PowerSeries.mk (fun n => (a n : ℤ)) =
      2 * X * (16 + 12 * X + 36 * X ^ 2 - 2 * X ^ 3 + 18 * X ^ 4 -
        33 * X ^ 5 + 16 * X ^ 6 - 3 * X ^ 7)) ∧
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
        15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a250354
