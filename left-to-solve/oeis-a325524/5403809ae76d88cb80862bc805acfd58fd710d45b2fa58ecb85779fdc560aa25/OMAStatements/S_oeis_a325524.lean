import Mathlib.Data.Nat.Basic

/-! Consecutive gaps for OEIS A325524. Source: https://oeis.org/A325524/internal -/

namespace OMA.S_oeis_a325524

/-- Greedy positive integers that are neither 3 nor 4 times an earlier member. -/
def selected (n : ℕ) : Prop :=
  if h : 0 < n then
    ¬ (3 ∣ n ∧ selected (n / 3)) ∧ ¬ (4 ∣ n ∧ selected (n / 4))
  else False
termination_by n
decreasing_by all_goals omega

def Mem (n : ℕ) : Prop := selected n

def Consecutive (x y : ℕ) : Prop :=
  x < y ∧ Mem x ∧ Mem y ∧ ∀ z : ℕ, x < z → z < y → ¬Mem z

theorem main : ∀ x y : ℕ, Consecutive x y → 1 ≤ y - x ∧ y - x ≤ 3 := by
  sorry

end OMA.S_oeis_a325524
