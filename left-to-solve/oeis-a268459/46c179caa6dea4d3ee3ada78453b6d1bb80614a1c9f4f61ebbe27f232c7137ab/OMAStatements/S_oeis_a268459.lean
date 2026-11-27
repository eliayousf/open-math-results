import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace OMA.S_oeis_a268459

/-- The ascending pair starting at `i` occurs in reverse at `j`. -/
def reversed {n : ℕ} (w : Fin 5 → Fin (n + 1)) (i j : Fin 4) : Prop :=
  (w i.castSucc).val + 1 = (w i.succ).val ∧
    w i.castSucc = w j.succ ∧ w i.succ = w j.castSucc

/-- The count is indexed from one, with coefficient zero at index zero in the series. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else
    (Nat.card {w : Fin 5 → Fin (n + 1) // ∀ i j : Fin 4, i < j → ¬ reversed w i j} : ℤ)

open PowerSeries in
theorem main :
    ((1 - X) ^ 6 * mk a = 4 * X * (4 + 20 * X + 9 * X ^ 2 - 4 * X ^ 3 + X ^ 4)) ∧
    (∀ n : ℕ, 6 < n →
      a n = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
        15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a268459
