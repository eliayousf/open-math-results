import OMAStatements.S_oeis_a203157
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace OpenMath.A203157

open OMA.S_oeis_a203157

private theorem tri_mul (n : ℕ) : 2 * tri n = (n : ℤ) * ((n : ℤ) + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [tri, Nat.cast_succ]
    linear_combination ih

private theorem step (n : ℕ) :
    products (n + 1) = ((products n).1 * tri (n + 1),
      (products n).2 * tri (n + 1) + (products n).1) := by
  change (let (p,e) := products n; (p * tri (n + 1), e * tri (n + 1) + p)) = _
  cases products n; rfl

private theorem balance (n : ℕ) : ((n : ℤ) + 1) * a n = 2 * (n : ℤ) * (products n).1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have ht := tri_mul (n + 1)
    have h : 2 * (((n : ℤ) + 2) * a (n + 1)) =
        2 * (2 * ((n : ℤ) + 1) * (products (n + 1)).1) := by
      unfold a at ih ⊢
      rw [step n]
      push_cast at ht
      linear_combination ((n : ℤ) + 2) ^ 2 * ih +
        (((n : ℤ) + 2) * (products n).2 -
          2 * ((n : ℤ) + 1) * (products n).1) * ht
    push_cast
    rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring]
    omega

private theorem shift_recur (n : ℕ) :
    2 * (n : ℤ) * a (n + 1) = ((n : ℤ) + 1)^3 * a n := by
  have hn := balance n
  have hs := balance (n + 1)
  have ht := tri_mul (n + 1)
  rw [step n] at hs
  push_cast at hs ht
  have h : ((n : ℤ) + 2) * (2 * (n : ℤ) * a (n + 1)) =
      ((n : ℤ) + 2) * (((n : ℤ) + 1)^3 * a n) := by
    linear_combination 2 * (n : ℤ) * hs +
      2 * (n : ℤ) * ((n : ℤ) + 1) * (products n).1 * ht -
      ((n : ℤ) + 1)^2 * ((n : ℤ) + 2) * hn
  exact mul_left_cancel₀ (by omega : (n : ℤ) + 2 ≠ 0) h

theorem main : ∀ n : ℕ, 1 < n →
    2 * (-(n : ℤ) + 1) * a n + (n : ℤ)^3 * a (n - 1) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega]
  push_cast
  linear_combination -shift_recur k

end OpenMath.A203157

theorem OMA.solution : type_of% @OMA.S_oeis_a203157.main := OpenMath.A203157.main
