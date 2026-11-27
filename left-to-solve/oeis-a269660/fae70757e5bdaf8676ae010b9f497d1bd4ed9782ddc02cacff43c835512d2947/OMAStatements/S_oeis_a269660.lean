import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace OMA.S_oeis_a269660

/-- The ascending consecutive pair starting at `i` also starts at `j`. -/
def repeated {n : ℕ} (w : Fin 7 → Fin (n + 1)) (i j : Fin 6) : Prop :=
  (w i.castSucc).val + 1 = (w i.succ).val ∧
    w i.castSucc = w j.castSucc ∧ w i.succ = w j.succ

/-- The count is indexed from one, with coefficient zero at index zero in the series. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else
    (Nat.card {w : Fin 7 → Fin (n + 1) // ∀ i j : Fin 6, i < j → ¬ repeated w i j} : ℤ)

open PowerSeries in
theorem main :
    ((1 - X) ^ 8 * mk a = 2 * X *
      (32 + 599 * X + 1354 * X ^ 2 + 438 * X ^ 3 + 48 * X ^ 4 + 71 * X ^ 5 -
        26 * X ^ 6 + 4 * X ^ 7)) ∧
    (∀ n : ℕ, 8 < n →
      a n = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) -
        70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a269660
