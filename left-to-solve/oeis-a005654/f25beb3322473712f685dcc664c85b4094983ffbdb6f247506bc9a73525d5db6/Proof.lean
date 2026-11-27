import OMAStatements.S_oeis_a005654
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

namespace OpenMath.A005654

open OMA.S_oeis_a005654

def centralHalf (n : ℕ) : ℚ := (Nat.centralBinom n : ℚ) / 2

def reversalFixed (n : ℕ) : ℚ := (Nat.choose (n - 1) (n / 2) : ℚ)

private theorem first_component (n : ℕ) (hn : 1 ≤ n) :
    (Nat.choose (2 * n - 1) n : ℚ) = centralHalf n := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  have hp : Nat.centralBinom (k + 1) = 2 * Nat.choose (2 * (k + 1) - 1) (k + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose,
      show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Nat.choose_succ_succ',
      show (2 * k + 1) + 1 - 1 = 2 * k + 1 by omega, ← Nat.choose_symm_half]
    omega
  unfold centralHalf
  rw [hp]
  push_cast
  ring

private theorem split (n : ℕ) (hn : 1 ≤ n) :
    a n = (centralHalf n + reversalFixed n) / 2 := by
  unfold a reversalFixed
  rw [first_component n hn]

private theorem central_step (k : ℕ) :
    ((k : ℚ) + 1) * centralHalf (k + 1) = (4 * (k : ℚ) + 2) * centralHalf k := by
  have h := Nat.succ_mul_centralBinom_succ k
  have hq := congrArg (fun x : ℕ => (x : ℚ)) h
  push_cast at hq
  unfold centralHalf
  linear_combination hq / 2

private theorem even_fixed (k : ℕ) (hk : 1 ≤ k) :
    reversalFixed (2 * k) = centralHalf k := by
  unfold reversalFixed
  rw [show 2 * k / 2 = k by omega, first_component k hk]

private theorem odd_fixed (k : ℕ) :
    reversalFixed (2 * k + 1) = 2 * centralHalf k := by
  unfold reversalFixed centralHalf
  rw [show (2 * k + 1) / 2 = k by omega, show 2 * k + 1 - 1 = 2 * k by omega,
    Nat.centralBinom_eq_two_mul_choose]
  ring

private theorem central_residual (k : ℕ) : residual centralHalf (k + 4) = 0 := by
  have h0 := central_step (k + 3)
  have h1 := central_step (k + 2)
  have h2 := central_step (k + 1)
  have h3 := central_step k
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.add_assoc, Nat.reduceAdd] at h0 h1 h2
  unfold residual
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega,
    Nat.cast_add, Nat.cast_ofNat]
  linear_combination ((k : ℚ) + 2) * h0 - ((k : ℚ) + 2) * h1 +
    (10 - 4 * ((k : ℚ) + 4)) * h2 + 4 * (k : ℚ) * h3

private theorem even_residual (k : ℕ) (hk : 1 ≤ k) :
    residual reversalFixed (2 * (k + 2)) = 0 := by
  have h0 := central_step (k + 1)
  have h1 := central_step k
  simp only [Nat.cast_add, Nat.add_assoc, Nat.reduceAdd] at h0
  unfold residual
  rw [show 2 * (k + 2) - 1 = 2 * (k + 1) + 1 by omega,
    show 2 * (k + 2) - 2 = 2 * (k + 1) by omega,
    show 2 * (k + 2) - 3 = 2 * k + 1 by omega,
    show 2 * (k + 2) - 4 = 2 * k by omega,
    even_fixed _ (by omega), odd_fixed, even_fixed _ (by omega), odd_fixed, even_fixed _ hk]
  push_cast
  linear_combination (4 * ((k : ℚ) + 1)) * h0 -
    (12 * (2 * ((k : ℚ) + 2) - 1)) * h1

private theorem odd_residual (k : ℕ) : residual reversalFixed (2 * (k + 2) + 1) = 0 := by
  have h0 := central_step (k + 1)
  have h1 := central_step k
  simp only [Nat.cast_add, Nat.add_assoc, Nat.reduceAdd] at h0
  unfold residual
  rw [show 2 * (k + 2) + 1 - 1 = 2 * (k + 2) by omega,
    show 2 * (k + 2) + 1 - 2 = 2 * (k + 1) + 1 by omega,
    show 2 * (k + 2) + 1 - 3 = 2 * (k + 1) by omega,
    show 2 * (k + 2) + 1 - 4 = 2 * k + 1 by omega,
    odd_fixed, even_fixed _ (by omega), odd_fixed, even_fixed _ (by omega), odd_fixed]
  push_cast
  linear_combination (-6 * (2 * ((k : ℚ) + 2) - 1)) * h0 +
    (8 * (4 * ((k : ℚ) + 2) - 5)) * h1

theorem recurrence (n : ℕ) (hn : 5 ≤ n) : residual a n = 0 := by
  have hc : residual centralHalf n = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 4 := ⟨n - 4, by omega⟩
    exact central_residual k
  have he : residual reversalFixed n = 0 := by
    let k := n / 2 - 2
    have hcases : n = 2 * (k + 2) ∨ n = 2 * (k + 2) + 1 := by omega
    rcases hcases with h | h
    · rw [h]
      exact even_residual k (by omega)
    · rw [h]
      exact odd_residual k
  unfold residual at *
  rw [split n (by omega), split (n - 1) (by omega), split (n - 2) (by omega),
    split (n - 3) (by omega), split (n - 4) (by omega)]
  linear_combination (hc + he) / 2

end OpenMath.A005654

theorem OMA.solution : type_of% @OMA.S_oeis_a005654.main := OpenMath.A005654.recurrence
