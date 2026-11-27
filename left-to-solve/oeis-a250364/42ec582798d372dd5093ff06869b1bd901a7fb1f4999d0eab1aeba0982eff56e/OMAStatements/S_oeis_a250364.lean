import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Fin

/-!
# Generating function and recurrence for OEIS A250364

Source: https://oeis.org/A250364

The zero-based position i has value i plus an offset from 0 through n.
Shifting all entries by one recovers the one-based intervals in the source
and preserves repetitions. The generating series begins at index one.
-/

namespace OMA.S_oeis_a250364

abbrev ArrayChoice (n : ℕ) := Fin 6 → Fin (n + 1)

def value {n : ℕ} (w : ArrayChoice n) (i : Fin 6) : ℕ := (w i).val + i.val

def positions {n : ℕ} (w : ArrayChoice n) (t : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter fun i => value w i = t

def bad {n : ℕ} (w : ArrayChoice n) : Prop := ∃ t : ℕ, 4 ≤ (positions w t).card

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.card { w : ArrayChoice n // ¬ bad w }

open PowerSeries in
theorem main :
    ((1 - X) ^ 7 * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (64 + 281 * X + 289 * X ^ 2 + 98 * X ^ 3 + 44 * X ^ 4 + 57 * X ^ 5 -
        405 * X ^ 6 + 482 * X ^ 7 - 232 * X ^ 8 + 42 * X ^ 9)) ∧
    (∀ n : ℕ, 10 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) -
        35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a250364
