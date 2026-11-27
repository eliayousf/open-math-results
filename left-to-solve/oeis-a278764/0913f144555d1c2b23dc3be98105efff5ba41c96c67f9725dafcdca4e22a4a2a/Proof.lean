import OMAStatements.S_oeis_a278764
import Mathlib.Data.Matrix.Reflection
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The recurrence and generating function for the floor Pisot sequence
`T(5,13)`, OEIS A278764. -/

namespace OpenMath.A278764

open Matrix

/-- The original floor recurrence. -/
def a : ℕ → ℕ
  | 0 => 5
  | 1 => 13
  | n + 2 => a (n + 1) ^ 2 / a n

private def b : ℕ → ℤ
  | 0 => 5
  | 1 => 13
  | 2 => 33
  | 3 => 83
  | 4 => 208
  | 5 => 521
  | n + 6 => 3 * b (n + 5) - 2 * b (n + 4) + 3 * b (n + 3) -
      3 * b (n + 2) + b (n + 1) - b n

private theorem b_step (n : ℕ) :
    b (n + 6) = 3 * b (n + 5) - 2 * b (n + 4) + 3 * b (n + 3) -
      3 * b (n + 2) + b (n + 1) - b n := rfl

private theorem b_affine (n : ℕ) :
    b (n + 5) = 2 * b (n + 4) + 3 * b (n + 2) + b n + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [Nat.add_assoc, Nat.reduceAdd]
      have hb := b_step n
      omega

private def u (n : ℕ) : ℤ := 5 * b n + 1

private theorem u_step (n : ℕ) : u (n + 5) = 2 * u (n + 4) + 3 * u (n + 2) + u n := by
  unfold u
  have h := b_affine n
  omega

private theorem u_ratios (n : ℕ) :
    5 * u n ≤ 2 * u (n + 1) ∧ 20 * u (n + 1) ≤ 51 * u n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 5
      · interval_cases n <;> norm_num [u, b]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      obtain ⟨h0lo, h0hi⟩ := ih k (by omega)
      obtain ⟨h2lo, h2hi⟩ := ih (k + 2) (by omega)
      obtain ⟨h4lo, h4hi⟩ := ih (k + 4) (by omega)
      have h5 := u_step k
      have h6 := u_step (k + 1)
      simp only [Nat.add_assoc, Nat.reduceAdd] at h2lo h2hi h4lo h4hi h6 ⊢
      exact ⟨by omega, by omega⟩

private theorem u_min (n : ℕ) : 26 ≤ u n := by
  induction n with
  | zero => decide
  | succ n ih =>
      have h := (u_ratios n).1
      omega

private theorem u_iterate (n k : ℕ) : (5 : ℤ) ^ k * u n ≤ 2 ^ k * u (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h := mul_le_mul_of_nonneg_left (u_ratios (n + k)).1
        (pow_nonneg (by decide : (0 : ℤ) ≤ 2) k)
      calc
        (5 : ℤ) ^ (k + 1) * u n = 5 * (5 ^ k * u n) := by ring
        _ ≤ 5 * (2 ^ k * u (n + k)) := mul_le_mul_of_nonneg_left ih (by decide)
        _ = 2 ^ k * (5 * u (n + k)) := by ring
        _ ≤ 2 ^ k * (2 * u (n + k + 1)) := h
        _ = 2 ^ (k + 1) * u (n + (k + 1)) := by rw [Nat.add_assoc]; ring

private def err (n : ℕ) : ℤ := u (n + 1) ^ 2 - u n * u (n + 2)

/-- The ten signed minors of two consecutive quintic recurrence vectors. -/
private def minors (n : ℕ) : Fin 10 → ℤ :=
  ![err n,
    u (n + 1) * u (n + 2) - u n * u (n + 3),
    u (n + 1) * u (n + 3) - u n * u (n + 4),
    u (n + 1) * u (n + 4) - u n * u (n + 5),
    u (n + 2) ^ 2 - u (n + 1) * u (n + 3),
    u (n + 2) * u (n + 3) - u (n + 1) * u (n + 4),
    u (n + 2) * u (n + 4) - u (n + 1) * u (n + 5),
    u (n + 3) ^ 2 - u (n + 2) * u (n + 4),
    u (n + 3) * u (n + 4) - u (n + 2) * u (n + 5),
    u (n + 4) ^ 2 - u (n + 3) * u (n + 5)]

private def stepMatrix : Matrix (Fin 10) (Fin 10) ℤ :=
  !![0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    -1, 0, 0, 0, 3, 0, 2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, -1, 0, 0, 0, 0, 0, 0, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, -1, 0, 0, 0, 0, -3, 0, 2;
    0, 0, 0, -1, 0, 0, 0, 0, -3, 0]

private def stepTwo : Matrix (Fin 10) (Fin 10) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, -1, 0, 0, 0, 0, 0, 0, 2, 0;
    0, -2, 0, 0, -1, 0, 0, 3, 4, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, -1, 0, 0, 0, 0, -3, 0, 2;
    0, 0, -2, 0, 0, -1, 0, -6, 0, 4;
    0, 0, 0, -1, 0, 0, 0, 0, -3, 0;
    0, 0, 0, -2, 0, 0, -1, 0, -6, -3;
    1, 0, 3, 0, -3, 0, -2, 9, 0, -6]

private def stepFour : Matrix (Fin 10) (Fin 10) ℤ :=
  !![0, 0, 0, -1, 0, 0, 0, 0, -3, 0;
    0, 0, 0, -2, 0, 0, -1, 0, -6, -3;
    0, 0, 0, -4, 0, 0, -2, 0, -13, -6;
    0, 0, 0, -11, 0, 0, -4, 0, -35, -13;
    1, 0, 3, 0, -3, 0, -2, 9, 0, -6;
    2, 1, 6, 3, -6, 0, -4, 18, 7, -12;
    4, 2, 13, 6, -12, 0, -8, 39, 14, -26;
    0, 2, 0, 6, 1, 0, 3, -3, 14, 9;
    -3, 4, -7, 12, 11, 1, 12, -27, 28, 32;
    -6, -3, -14, -9, 18, 2, 12, -41, -21, 25]

private def stepEight : Matrix (Fin 10) (Fin 10) ℤ :=
  !![9, -12, 21, -25, -33, -3, -32, 81, -49, -83;
    32, -17, 71, -29, -108, -12, -92, 246, -49, -215;
    67, -38, 149, -70, -227, -25, -196, 519, -126, -462;
    167, -109, 375, -206, -571, -61, -500, 1322, -378, -1198;
    25, 32, 49, 83, -66, -12, -29, 114, 182, -17;
    29, 92, 49, 215, -55, -17, 13, 39, 449, 148;
    70, 196, 126, 462, -143, -38, 9, 151, 969, 267;
    -83, 29, -182, 17, 274, 32, 215, -612, -19, 478;
    -215, -13, -449, -148, 674, 92, 479, -1402, -435, 937;
    -17, -215, 19, -478, -32, 29, -148, 331, -972, -650]

private def stepSixteen : Matrix (Fin 10) (Fin 10) ℤ :=
  !![-1000, 15250, -7023, 33938, 9250, -1543, 16058, -41432, 69042, 60409;
    -16058, 31772, -45159, 60853, 63424, 2227, 64511, -182770, 112710, 189860;
    -30573, 69849, -89046, 136956, 124491, 3015, 131249, -369477, 257815, 395778;
    -70396, 186991, -213219, 374726, 297095, 3673, 325922, -909613, 715733, 1006721;
    -33938, -16058, -69042, -60409, 100814, 15250, 60853, -197876, -150654, 96652;
    -60853, -64511, -112710, -189860, 166501, 31772, 76547, -274706, -438331, 42650;
    -136956, -131249, -257815, -395778, 380295, 69849, 184866, -648954, -921821, 146153;
    60409, -60853, 150654, -96652, -215165, -16058, -189860, 552776, -153000, -499184;
    189860, -76547, 438331, -42650, -630433, -64511, -492430, 1481494, 56916, -1151368;
    96652, 189860, 153000, 499184, -229547, -60853, -42650, 243835, 1101774, 246776]

private theorem minors_step (n : ℕ) : minors (n + 1) = stepMatrix *ᵥ minors n := by
  have h5 := u_step n
  have h6 := u_step (n + 1)
  funext i
  fin_cases i <;>
    simp [minors, err, stepMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Nat.add_assoc]
  all_goals (rw [h6, h5]; ring)

private theorem minors_shift (n k : ℕ) : minors (n + k) = stepMatrix ^ k *ᵥ minors n := by
  induction k with
  | zero => simp
  | succ k ih =>
      change minors (n + k + 1) = _
      rw [minors_step, ih, Matrix.mulVec_mulVec, pow_succ']

private theorem stepTwo_eq : stepMatrix ^ 2 = stepTwo := by decide

private theorem stepFour_eq : stepMatrix ^ 4 = stepFour := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, stepTwo_eq]
  decide

private theorem stepEight_eq : stepMatrix ^ 8 = stepEight := by
  rw [show (8 : ℕ) = 4 * 2 by decide, pow_mul, stepFour_eq]
  decide

private theorem stepSixteen_eq : stepMatrix ^ 16 = stepSixteen := by
  rw [show (16 : ℕ) = 8 * 2 by decide, pow_mul, stepEight_eq]
  decide

set_option maxHeartbeats 8000000 in
private theorem matrix_certificate :
    stepMatrix ^ 19 = (1526 : ℤ) • 1 - (4075 : ℤ) • stepMatrix -
      (4983 : ℤ) • stepMatrix ^ 2 + (18603 : ℤ) • stepMatrix ^ 3 +
      (753 : ℤ) • stepMatrix ^ 4 - (28737 : ℤ) • stepMatrix ^ 5 +
      (11732 : ℤ) • stepMatrix ^ 6 + (1552 : ℤ) • stepMatrix ^ 7 -
      (25 : ℤ) • stepMatrix ^ 8 + (5336 : ℤ) • stepMatrix ^ 9 := by
  have h : stepSixteen * stepTwo * stepMatrix =
      (1526 : ℤ) • 1 - (4075 : ℤ) • stepMatrix -
      (4983 : ℤ) • stepTwo + (18603 : ℤ) • (stepTwo * stepMatrix) +
      (753 : ℤ) • stepFour - (28737 : ℤ) • (stepFour * stepMatrix) +
      (11732 : ℤ) • (stepFour * stepTwo) + (1552 : ℤ) • (stepFour * stepTwo * stepMatrix) -
      (25 : ℤ) • stepEight + (5336 : ℤ) • (stepEight * stepMatrix) := by decide
  simp only [← stepTwo_eq, ← stepFour_eq, ← stepEight_eq, ← stepSixteen_eq,
    ← pow_add, ← pow_succ] at h
  exact h

private theorem err_stride (n : ℕ) :
    err (n + 19) = 1526 * err n - 4075 * err (n + 1) - 4983 * err (n + 2) +
      18603 * err (n + 3) + 753 * err (n + 4) - 28737 * err (n + 5) +
      11732 * err (n + 6) + 1552 * err (n + 7) - 25 * err (n + 8) +
      5336 * err (n + 9) := by
  have hv := congrArg (fun M : Matrix (Fin 10) (Fin 10) ℤ => M *ᵥ minors n) matrix_certificate
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hv
  have ha := congrFun hv (0 : Fin 10)
  simp only [Pi.add_apply, Pi.sub_apply, zsmul_eq_mul, ← minors_shift, ← minors_step] at ha
  exact ha

private theorem weighted_bound (n : ℕ) :
    1526 * u n + 4075 * u (n + 1) + 4983 * u (n + 2) + 18603 * u (n + 3) +
      753 * u (n + 4) + 28737 * u (n + 5) + 11732 * u (n + 6) + 1552 * u (n + 7) +
      25 * u (n + 8) + 5336 * u (n + 9) ≤ u (n + 19) := by
  have h0 := u_iterate n 19
  have h1 := u_iterate (n + 1) 18
  have h2 := u_iterate (n + 2) 17
  have h3 := u_iterate (n + 3) 16
  have h4 := u_iterate (n + 4) 15
  have h5 := u_iterate (n + 5) 14
  have h6 := u_iterate (n + 6) 13
  have h7 := u_iterate (n + 7) 12
  have h8 := u_iterate (n + 8) 11
  have h9 := u_iterate (n + 9) 10
  have hp := u_min (n + 19)
  norm_num [Nat.add_assoc] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hp]

set_option maxHeartbeats 8000000 in
private theorem err_bound (n : ℕ) : -9 * u n ≤ 4 * err n ∧ 4 * err n ≤ 9 * u n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 19
      · interval_cases n <;> norm_num [err, u, b]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 19 := ⟨n - 19, by omega⟩
      obtain ⟨l0, r0⟩ := ih k (by omega)
      obtain ⟨l1, r1⟩ := ih (k + 1) (by omega)
      obtain ⟨l2, r2⟩ := ih (k + 2) (by omega)
      obtain ⟨l3, r3⟩ := ih (k + 3) (by omega)
      obtain ⟨l4, r4⟩ := ih (k + 4) (by omega)
      obtain ⟨l5, r5⟩ := ih (k + 5) (by omega)
      obtain ⟨l6, r6⟩ := ih (k + 6) (by omega)
      obtain ⟨l7, r7⟩ := ih (k + 7) (by omega)
      obtain ⟨l8, r8⟩ := ih (k + 8) (by omega)
      obtain ⟨l9, r9⟩ := ih (k + 9) (by omega)
      have hs := err_stride k
      have hw := weighted_bound k
      constructor
      · linarith only [hs, hw, l0, r1, r2, l3, l4, r5, l6, l7, r8, l9]
      · linarith only [hs, hw, r0, l1, l2, r3, r4, l5, r6, r7, l8, r9]

private def d (n : ℕ) : ℤ := b (n + 1) ^ 2 - b n * b (n + 2)

private theorem error_relation (n : ℕ) : 25 * d n = err n + u n + u (n + 2) - 2 * u (n + 1) := by
  unfold d err u
  ring

private theorem d_bounds (n : ℕ) : 0 ≤ d n ∧ d n < b n := by
  have hlo := err_bound n
  have hrel := error_relation n
  have h0 := u_ratios n
  have h1 := u_ratios (n + 1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1
  have hmin := u_min n
  have he : u n = 5 * b n + 1 := rfl
  obtain ⟨hl, hu⟩ := hlo
  exact ⟨by omega, by omega⟩

private theorem a_eq_b (n : ℕ) : (a n : ℤ) = b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 2
      · interval_cases n <;> rfl
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      change (↑(a (k + 1) ^ 2 / a k) : ℤ) = b (k + 2)
      rw [Int.natCast_ediv, Int.natCast_pow, ih (k + 1) (by omega), ih k (by omega)]
      have hk := u_min k
      have hb : 0 < b k := by unfold u at hk; omega
      obtain ⟨hlo, hhi⟩ := d_bounds k
      unfold d at hlo hhi
      apply (Int.ediv_eq_iff_of_pos hb).2
      rw [mul_comm (b (k + 2))]
      exact ⟨by omega, by omega⟩

theorem linear_recurrence (n : ℕ) :
    (a (n + 6) : ℤ) =
      3 * (a (n + 5) : ℤ) - 2 * (a (n + 4) : ℤ) + 3 * (a (n + 3) : ℤ) -
      3 * (a (n + 2) : ℤ) + (a (n + 1) : ℤ) - (a n : ℤ) := by
  simp only [a_eq_b]
  exact b_step n

open PowerSeries in
theorem generating_function :
    (1 - X) * (1 - 2 * X - 3 * X ^ 3 - X ^ 5) *
      mk (fun n => (a n : ℤ)) = (5 - 2 * X + 4 * X ^ 2 - 5 * X ^ 3 + X ^ 4 - 2 * X ^ 5 : ℤ⟦X⟧) := by
  simp only [a_eq_b]
  have hden : ((1 - X) * (1 - 2 * X - 3 * X ^ 3 - X ^ 5) : ℤ⟦X⟧) =
      1 - C 3 * X ^ 1 + C 2 * X ^ 2 - C 3 * X ^ 3 + C 3 * X ^ 4 - X ^ 5 + X ^ 6 := by
    simp
    ring
  have hnum : (5 - 2 * X + 4 * X ^ 2 - 5 * X ^ 3 + X ^ 4 - 2 * X ^ 5 : ℤ⟦X⟧) =
      C 5 - C 2 * X ^ 1 + C 4 * X ^ 2 - C 5 * X ^ 3 + X ^ 4 - C 2 * X ^ 5 := by simp
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
  by_cases h : n < 6
  · interval_cases n <;> norm_num [b]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  simp only [if_pos (show 1 ≤ k + 6 by omega), if_pos (show 2 ≤ k + 6 by omega),
    if_pos (show 3 ≤ k + 6 by omega), if_pos (show 4 ≤ k + 6 by omega),
    if_pos (show 5 ≤ k + 6 by omega), if_pos (show 6 ≤ k + 6 by omega),
    if_neg (show k + 6 ≠ 0 by omega), if_neg (show k + 6 ≠ 1 by omega),
    if_neg (show k + 6 ≠ 2 by omega), if_neg (show k + 6 ≠ 3 by omega),
    if_neg (show k + 6 ≠ 4 by omega), if_neg (show k + 6 ≠ 5 by omega)]
  change b (k + 6) - 3 * b (k + 5) + 2 * b (k + 4) - 3 * b (k + 3) +
    3 * b (k + 2) - b (k + 1) + b k = _
  have hb := b_step k
  omega

open PowerSeries in
theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 2 * (a (n - 2) : ℤ) +
      3 * (a (n - 3) : ℤ) - 3 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ) - (a (n - 6) : ℤ)) ∧
    ((1 - X) * (1 - 2 * X - 3 * X ^ 3 - X ^ 5) *
      PowerSeries.mk (fun n => (a n : ℤ)) = 5 - 2 * X + 4 * X ^ 2 - 5 * X ^ 3 + X ^ 4 - 2 * X ^ 5) := by
  refine ⟨?_, generating_function⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  exact linear_recurrence k

end OpenMath.A278764

private theorem source_a_eq : OMA.S_oeis_a278764.a = OpenMath.A278764.a := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 2
      · interval_cases n <;> rfl
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      change OMA.S_oeis_a278764.a (k + 1) ^ 2 / OMA.S_oeis_a278764.a k =
        OpenMath.A278764.a (k + 1) ^ 2 / OpenMath.A278764.a k
      rw [ih (k + 1) (by omega), ih k (by omega)]

theorem OMA.solution : type_of% @OMA.S_oeis_a278764.main := by
  rw [source_a_eq]
  exact OpenMath.A278764.main
