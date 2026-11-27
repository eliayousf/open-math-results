import OMAStatements.S_oeis_a278692
import Mathlib.Data.Matrix.Reflection
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! The linear recurrence and generating function for the floor Pisot sequence
`T(4,14)`, OEIS A278692. -/

namespace OpenMath.A278692

open Matrix

/-- The original floor recurrence. -/
def a : ℕ → ℕ
  | 0 => 4
  | 1 => 14
  | n + 2 => a (n + 1) ^ 2 / a n

private def b : ℕ → ℤ
  | 0 => 4
  | 1 => 14
  | 2 => 49
  | 3 => 171
  | n + 4 => 4 * b (n + 3) - 2 * b (n + 2) + b (n + 1) - b n

private theorem b_step (n : ℕ) :
    b (n + 4) = 4 * b (n + 3) - 2 * b (n + 2) + b (n + 1) - b n := rfl

private def d (n : ℕ) : ℤ := b (n + 1) ^ 2 - b n * b (n + 2)

/-- The six signed minors of the two consecutive recurrence vectors. -/
private def minors (n : ℕ) : Fin 6 → ℤ :=
  ![d n,
    b (n + 1) * b (n + 2) - b n * b (n + 3),
    b (n + 1) * b (n + 3) - b n * b (n + 4),
    b (n + 2) ^ 2 - b (n + 1) * b (n + 3),
    b (n + 2) * b (n + 3) - b (n + 1) * b (n + 4),
    b (n + 3) ^ 2 - b (n + 2) * b (n + 4)]

private def stepMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    1, 0, 0, -2, 4, 0;
    0, 0, 0, 0, 0, 1;
    0, 1, 0, -1, 0, 4;
    0, 0, 1, 0, -1, 2]

private theorem minors_step (n : ℕ) :
    minors (n + 1) = stepMatrix *ᵥ minors n := by
  have h4 := b_step n
  have h5 := b_step (n + 1)
  funext i
  fin_cases i <;>
    simp [minors, d, stepMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Nat.add_assoc]
  all_goals (rw [h5, h4]; ring)

private theorem minors_shift (n k : ℕ) :
    minors (n + k) = stepMatrix ^ k *ᵥ minors n := by
  induction k with
  | zero => simp
  | succ k ih =>
      change minors (n + k + 1) = _
      rw [minors_step, ih, Matrix.mulVec_mulVec, pow_succ']

private def fiveStepMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, 2, 0, -5, 7, 7;
    7, 9, 2, -19, 23, 35;
    25, 31, 10, -67, 80, 126;
    0, 7, 7, -5, -5, 37;
    2, 23, 35, -20, -18, 143;
    7, -5, 37, -9, -2, 49]

set_option maxHeartbeats 4000000 in
private theorem fiveStep_eq : stepMatrix ^ 5 = fiveStepMatrix := by decide

set_option maxHeartbeats 8000000 in
private theorem matrix_certificate :
    fiveStepMatrix ^ 6 + 1 =
      (47 : ℤ) • fiveStepMatrix ^ 5 + (7197 : ℤ) • fiveStepMatrix ^ 4 +
        (264298 : ℤ) • fiveStepMatrix ^ 3 + (7197 : ℤ) • fiveStepMatrix ^ 2 +
        (47 : ℤ) • fiveStepMatrix := by
  decide

private theorem d_stride (n : ℕ) :
    d (n + 30) = 47 * d (n + 25) + 7197 * d (n + 20) +
      264298 * d (n + 15) + 7197 * d (n + 10) + 47 * d (n + 5) - d n := by
  have h := matrix_certificate
  rw [← fiveStep_eq, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul] at h
  have hv := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ => M *ᵥ minors n) h
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hv
  have ha := congrFun hv (0 : Fin 6)
  simp only [Pi.add_apply, zsmul_eq_mul, ← minors_shift] at ha
  change d (n + 30) + d n = 47 * d (n + 25) + 7197 * d (n + 20) +
    264298 * d (n + 15) + 7197 * d (n + 10) + 47 * d (n + 5) at ha
  omega

set_option maxHeartbeats 8000000 in
private theorem d_seed (n : ℕ) (hl : 5 ≤ n) (hu : n < 30) :
    0 < d n ∧ 80 * d n ≤ d (n + 5) ∧ d (n + 5) ≤ 200 * d n := by
  interval_cases n <;> norm_num [d, b]

private theorem d_growth (n : ℕ) (hn : 5 ≤ n) :
    0 < d n ∧ 80 * d n ≤ d (n + 5) ∧ d (n + 5) ≤ 200 * d n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 30
      · exact d_seed n hn h
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 25 := ⟨n - 25, by omega⟩
      obtain ⟨h0, h05, _⟩ := ih k (by omega) (by omega)
      obtain ⟨h5, h510, _⟩ := ih (k + 5) (by omega) (by omega)
      obtain ⟨h10, h1015, _⟩ := ih (k + 10) (by omega) (by omega)
      obtain ⟨h15, h1520, _⟩ := ih (k + 15) (by omega) (by omega)
      obtain ⟨h20, h2025, hcap⟩ := ih (k + 20) (by omega) (by omega)
      simp only [Nat.add_assoc, Nat.reduceAdd] at h510 h1015 h1520 h2025 hcap ⊢
      have h25 : 0 < d (k + 25) := by omega
      have hcost : d k ≤ d (k + 25) := by omega
      have hlower20 : 35 * d (k + 25) ≤ 7197 * d (k + 20) := by omega
      have hterm20 : 7197 * d (k + 20) ≤ 90 * d (k + 25) := by omega
      have hterm15 : 264298 * d (k + 15) ≤ 42 * d (k + 25) := by omega
      have hterm10 : 7197 * d (k + 10) ≤ d (k + 25) := by omega
      have hterm5 : 47 * d (k + 5) ≤ d (k + 25) := by omega
      have hrec := d_stride k
      exact ⟨h25, by omega, by omega⟩

private theorem b_growth (n : ℕ) : 0 < b n ∧ 3 * b n ≤ b (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 3
      · interval_cases n <;> norm_num [b]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      obtain ⟨h0, h01⟩ := ih k (by omega)
      obtain ⟨h1, h12⟩ := ih (k + 1) (by omega)
      obtain ⟨h2, h23⟩ := ih (k + 2) (by omega)
      have hrec := b_step k
      simp only [Nat.add_assoc, Nat.reduceAdd] at h12 h23 hrec ⊢
      exact ⟨by omega, by omega⟩

private theorem b_five (n : ℕ) : 243 * b n ≤ b (n + 5) := by
  have h0 := (b_growth n).2
  have h1 := (b_growth (n + 1)).2
  have h2 := (b_growth (n + 2)).2
  have h3 := (b_growth (n + 3)).2
  have h4 := (b_growth (n + 4)).2
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h2 h3 h4
  omega

private theorem d_bounds (n : ℕ) : 0 ≤ d n ∧ d n < b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 10
      · interval_cases n <;> norm_num [d, b]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      have hsmall := ih k (by omega)
      have hd := d_growth k (by omega)
      have hb := b_five k
      have hp := (b_growth k).1
      exact ⟨by omega, by omega⟩

private theorem a_eq_b (n : ℕ) : (a n : ℤ) = b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 2
      · interval_cases n <;> rfl
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      change (↑(a (k + 1) ^ 2 / a k) : ℤ) = b (k + 2)
      rw [Int.natCast_ediv, Int.natCast_pow, ih (k + 1) (by omega), ih k (by omega)]
      have hb := (b_growth k).1
      have hd := d_bounds k
      obtain ⟨hlo, hhi⟩ := hd
      unfold d at hlo hhi
      apply (Int.ediv_eq_iff_of_pos hb).2
      rw [mul_comm (b (k + 2))]
      exact ⟨by omega, by omega⟩

theorem linear_recurrence (n : ℕ) :
    (a (n + 4) : ℤ) =
      4 * (a (n + 3) : ℤ) - 2 * (a (n + 2) : ℤ) + (a (n + 1) : ℤ) - (a n : ℤ) := by
  simp only [a_eq_b]
  exact b_step n

open PowerSeries in
theorem generating_function :
    (1 - 4 * X + 2 * X ^ 2 - X ^ 3 + X ^ 4) *
      mk (fun n => (a n : ℤ)) = (4 - 2 * X + X ^ 2 - X ^ 3 : ℤ⟦X⟧) := by
  simp only [a_eq_b]
  have hden : (1 - 4 * X + 2 * X ^ 2 - X ^ 3 + X ^ 4 : ℤ⟦X⟧) =
      1 - C 4 * X ^ 1 + C 2 * X ^ 2 - X ^ 3 + X ^ 4 := by simp
  have hnum : (4 - 2 * X + X ^ 2 - X ^ 3 : ℤ⟦X⟧) =
      C 4 - C 2 * X ^ 1 + X ^ 2 - X ^ 3 := by simp
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
  by_cases h : n < 4
  · interval_cases n <;> norm_num [b]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [if_pos (show 1 ≤ k + 4 by omega), if_pos (show 2 ≤ k + 4 by omega),
    if_pos (show 3 ≤ k + 4 by omega), if_pos (show 4 ≤ k + 4 by omega),
    if_neg (show k + 4 ≠ 0 by omega), if_neg (show k + 4 ≠ 1 by omega),
    if_neg (show k + 4 ≠ 2 by omega), if_neg (show k + 4 ≠ 3 by omega)]
  change b (k + 4) - 4 * b (k + 3) + 2 * b (k + 2) - b (k + 1) + b k = _
  have hb := b_step k
  omega

open PowerSeries in
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 4 * (a (n - 1) : ℤ) - 2 * (a (n - 2) : ℤ) +
      (a (n - 3) : ℤ) - (a (n - 4) : ℤ)) ∧
    ((1 - 4 * X + 2 * X ^ 2 - X ^ 3 + X ^ 4) *
      PowerSeries.mk (fun n => (a n : ℤ)) = 4 - 2 * X + X ^ 2 - X ^ 3) := by
  refine ⟨?_, generating_function⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  exact linear_recurrence k

end OpenMath.A278692

private theorem sameA : OMA.S_oeis_a278692.a = OpenMath.A278692.a := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < 2
    · interval_cases n <;> rfl
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    change OMA.S_oeis_a278692.a (k + 1) ^ 2 / OMA.S_oeis_a278692.a k =
      OpenMath.A278692.a (k + 1) ^ 2 / OpenMath.A278692.a k
    rw [ih (k + 1) (by omega), ih k (by omega)]

theorem OMA.solution : type_of% @OMA.S_oeis_a278692.main := by
  rw [sameA]
  exact OpenMath.A278692.main

