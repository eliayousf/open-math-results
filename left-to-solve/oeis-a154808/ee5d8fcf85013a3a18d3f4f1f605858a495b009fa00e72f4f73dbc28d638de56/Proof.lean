import OMAStatements.S_oeis_a154808
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

namespace OpenMath.BinaryRuns

open OMA.S_oeis_a154808 (digits a)

private theorem block_ones (w : ℕ) :
    ((Nat.ofDigits (2 : ℕ) (List.replicate w 1) : ℕ) : ℤ) = 2 ^ w - 1 := by
  induction w with
  | zero => decide
  | succ n ih =>
    simp only [List.replicate_succ, Nat.ofDigits_cons, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, ih, pow_succ]
    ring

private theorem step (w n : ℕ) :
    a w (n + 1) = (2 : ℤ)^w * a w n + if n % 2 = 0 then (2:ℤ)^w - 1 else 0 := by
  unfold a
  rw [digits, Nat.ofDigits_append]
  by_cases hn : n % 2 = 0
  · simp [hn, block_ones, add_comm]
  · simp [hn]

private theorem odd_sign (n : ℕ) :
    (-1 : ℤ)^n = if n % 2 = 0 then 1 else -1 := by
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, show n = 2 * (n / 2) by omega, pow_mul]
    norm_num
  · rw [if_neg hn, show n = 2 * (n / 2) + 1 by omega, pow_succ, pow_mul]
    norm_num

private theorem closed (w n : ℕ) :
    2 * ((2:ℤ)^w+1) * a w n = 2 * ((2:ℤ)^w)^(n+1) -
      ((2:ℤ)^w-1)*(-1:ℤ)^n - ((2:ℤ)^w+1) := by
  induction n with
  | zero => simp [a, digits]; ring
  | succ n ih =>
    have hbit : 2 * (if n % 2 = 0 then (2:ℤ)^w - 1 else 0) =
        ((2:ℤ)^w-1)*(1+(-1:ℤ)^n) := by
      rw [odd_sign]
      split <;> ring
    rw [step, pow_succ ((2:ℤ)^w) (n+1), pow_succ (-1:ℤ) n]
    linear_combination ((2:ℤ)^w) * ih + ((2:ℤ)^w+1) * hbit

private theorem recurrence (w k : ℕ) :
    a w (k+3) - (2:ℤ)^w*a w (k+2) - a w (k+1) + (2:ℤ)^w*a w k = 0 := by
  have h0 := step w k
  have h2 := step w (k+2)
  rw [show (k+2)%2 = k%2 by omega] at h2
  linear_combination h2 - h0


open PowerSeries in
theorem generating (w : ℕ) :
    (1-X^2) * (1-C ((2:ℤ)^w)*X) * mk (a w) = C ((2:ℤ)^w-1)*X^1 := by
  have hD : ((1-X^2) * (1-C ((2:ℤ)^w)*X) : ℤ⟦X⟧) =
      1 - C ((2:ℤ)^w)*X^1 - X^2 + C ((2:ℤ)^w)*X^3 := by
    simp
    ring
  have h0 : a w 0 = 0 := rfl
  have h1 : a w 1 = (2:ℤ)^w-1 := by simpa [h0] using step w 0
  have h2 : a w 2 = (2:ℤ)^w*((2:ℤ)^w-1) := by simpa [h1] using step w 1
  rw [hD]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n < 3
  · interval_cases n <;> norm_num [h0,h1,h2]
  obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
  simp only [if_pos (show 1 ≤ k+3 by omega), if_pos (show 2 ≤ k+3 by omega),
    if_pos (show 3 ≤ k+3 by omega), if_neg (show k+3 ≠ 1 by omega), mul_zero]
  exact recurrence w k

open PowerSeries in
theorem main4 :
    (∀ n : ℕ, 1 ≤ n → 34*a 4 n = 2*(2:ℤ)^(4*n+4)-15*(-1:ℤ)^n-17) ∧
    ((1-X^2)*(1-C (16:ℤ)*X)*mk (a 4)=C 15*X^1) := by
  refine ⟨?_, ?_⟩
  · intro n _
    have h := closed 4 n
    rw [← pow_mul, show 4*(n+1)=4*n+4 by omega] at h
    norm_num at h
    exact h
  · have h := generating 4
    norm_num at h ⊢
    exact h

open PowerSeries in
theorem main5 :
    (∀ n : ℕ, 1 ≤ n → 66*a 5 n = (2:ℤ)^(6+5*n)-31*(-1:ℤ)^n-33) ∧
    ((1-X^2)*(1-C (32:ℤ)*X)*mk (a 5)=C 31*X^1) := by
  refine ⟨?_, ?_⟩
  · intro n _
    have h := closed 5 n
    rw [← pow_mul, show 5*(n+1)=5*n+5 by omega] at h
    rw [show 6+5*n=(5*n+5)+1 by omega, pow_succ]
    norm_num at h
    linarith only [h]
  · have h := generating 5
    norm_num at h ⊢
    exact h

end OpenMath.BinaryRuns

theorem OMA.solution : type_of% @OMA.S_oeis_a154808.main := by
  exact OpenMath.BinaryRuns.main5
