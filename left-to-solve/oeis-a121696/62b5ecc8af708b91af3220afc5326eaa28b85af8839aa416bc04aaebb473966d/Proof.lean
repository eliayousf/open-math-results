import OMAStatements.S_oeis_a121696
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OpenMath.A121696

open OMA.S_oeis_a121696 (a)

private theorem stepFour (t : ℕ) :
    a (t + 4) = a (t + 2) + ((t : ℤ) + 4) * (t + 2).factorial * ↑((t+3)/2) := by
  change a (t + 2) + ((↑(t+1) : ℤ) + 3) * (t + 2).factorial * ↑((t+3)/2) = _
  push_cast
  ring

private theorem pairEven (t : ℕ) :
    a (t + 2) + a (t + 1) = ((t + 1).factorial : ℤ) * ↑((t + 3) / 2) := by
  induction t using Nat.twoStepInduction with
  | zero => norm_num [a]
  | one => norm_num [a]
  | more t prev _ =>
    change a (t + 4) + a (t + 3) = ((t + 3).factorial : ℤ) * ↑((t + 5) / 2)
    have step₁ : a (t + 3) = a (t + 1) + ((t : ℤ) + 3) * (t + 1).factorial * ↑((t+2)/2) := rfl
    have hfloor₁ : (↑((t + 5) / 2) : ℤ) = ↑((t + 3) / 2) + 1 := by omega
    have hfloor₂ : (↑((t + 2) / 2) : ℤ) = ↑t + 2 - ↑((t + 3) / 2) := by omega
    rw [stepFour, step₁, hfloor₁, hfloor₂]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at prev ⊢
    linear_combination prev

theorem evenRecurrence (n : ℕ) (hn : 4 ≤ n) :
    a n - ((n : ℤ) - 1) ^ 2 * a (n - 2) - (n : ℤ) * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 4 t, show t + 4 - 2 = t + 2 by omega, show t + 4 - 3 = t + 1 by omega]
  rw [stepFour]
  have h := pairEven t
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at h ⊢
  linear_combination -(((t : ℤ) + 4) * ((t : ℤ) + 2)) * h

end OpenMath.A121696

theorem OMA.solution : type_of% @OMA.S_oeis_a121696.main := OpenMath.A121696.evenRecurrence
