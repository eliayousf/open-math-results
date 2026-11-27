import OMAStatements.S_oeis_a121695
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OpenMath.A121695

open OMA.S_oeis_a121695 (a b)

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

private theorem pairOdd (t : ℕ) :
    b (t + 2) + b (t + 1) = ((t + 1).factorial : ℤ) * ↑((t + 4) / 2) := by
  have hfloor : (↑((t + 4) / 2) : ℤ) = ↑t + 3 - ↑((t + 3) / 2) := by omega
  have h := pairEven t
  rw [hfloor]
  simp only [b, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add] at h ⊢
  linear_combination -h

theorem oddRecurrence (n : ℕ) (hn : 5 ≤ n) :
    b n + b (n - 1) - (n : ℤ) * ((n : ℤ) - 2) * b (n - 2) -
      (2 * (n : ℤ) - 3) * ((n : ℤ) - 2) * b (n - 3) -
      ((n : ℤ) - 2) * ((n : ℤ) - 3) * b (n - 4) = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 5 t, show t + 5 - 1 = t + 4 by omega, show t + 5 - 2 = t + 3 by omega,
    show t + 5 - 3 = t + 2 by omega, show t + 5 - 4 = t + 1 by omega]
  have h₁ := pairOdd (t+3)
  have h₂ := pairOdd (t+1)
  have h₃ := pairOdd t
  have hfloor₁ : (↑((t + 3 + 4) / 2) : ℤ) = ↑((t + 1 + 4) / 2) + 1 := by omega
  have hfloor₂ : (↑((t + 4) / 2) : ℤ) = ↑t + 4 - ↑((t + 1 + 4) / 2) := by omega
  rw [hfloor₁] at h₁
  rw [hfloor₂] at h₃
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at h₁ h₂ h₃ ⊢
  linear_combination h₁ - (((t : ℤ) + 5) * ((t : ℤ) + 3)) * h₂ -
    (((t : ℤ) + 3) * ((t : ℤ) + 2)) * h₃

end OpenMath.A121695

theorem OMA.solution : type_of% @OMA.S_oeis_a121695.main := OpenMath.A121695.oddRecurrence
