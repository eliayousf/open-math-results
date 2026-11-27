import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace OMA.S_oeis_a269659

/-- The ascending consecutive pair starting at `i` also starts at `j`. -/
def repeated {n : ℕ} (w : Fin 6 → Fin (n + 1)) (i j : Fin 5) : Prop :=
  (w i.castSucc).val + 1 = (w i.succ).val ∧
    w i.castSucc = w j.castSucc ∧ w i.succ = w j.succ

/-- The count is indexed from one, with coefficient zero at index zero in the series. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else
    (Nat.card {w : Fin 6 → Fin (n + 1) // ∀ i j : Fin 5, i < j → ¬ repeated w i j} : ℤ)

open PowerSeries in
theorem main :
    ((1 - X) ^ 7 * mk a = 2 * X *
      (21 + 166 * X + 158 * X ^ 2 + 17 * X ^ 4 - 2 * X ^ 5)) ∧
    (∀ n : ℕ, 7 < n →
      a n = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) -
        35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a269659
