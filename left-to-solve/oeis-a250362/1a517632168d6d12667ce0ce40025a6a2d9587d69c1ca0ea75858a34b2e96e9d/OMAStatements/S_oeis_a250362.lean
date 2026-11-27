import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Generating function and recurrence for OEIS A250362

Source: https://oeis.org/A250362

Position i is indexed from zero. It ranges from i to i+n, which shifts
every original entry down by one and preserves equality and repetitions.
With four entries, a value occurs more than three times exactly when the
whole array is constant. The ordinary series starts at degree one.
-/

namespace OMA.S_oeis_a250362

abbrev ArrayChoice (n : ℕ) := Fin 4 → Fin (n + 1)

def constantArray {n : ℕ} (w : ArrayChoice n) : Prop :=
  ∀ i : Fin 4, (w i).val + i.val = (w 0).val

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.card { w : ArrayChoice n // ¬ constantArray w }

open PowerSeries in
theorem main :
    ((1 - X) ^ 5 * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (16 + X + 10 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + X ^ 5)) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
        5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a250362
