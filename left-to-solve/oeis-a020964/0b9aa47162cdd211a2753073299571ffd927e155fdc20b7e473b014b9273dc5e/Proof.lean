import OMAStatements.S_oeis_a020964
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Wu's recurrence for the floor-sum sequence A020964. -/

open Finset

namespace OpenMath.A020964

noncomputable def α : ℝ := 1 + Real.sqrt 2

private noncomputable def β : ℝ := 1 - Real.sqrt 2

noncomputable def term (j : ℕ) : ℤ := ⌊3 * α ^ j⌋

/-- The negative exponent `-1` contributes one; earlier contributions vanish. -/
noncomputable def a (n : ℕ) : ℤ := 1 + ∑ j ∈ range n, term j

private theorem sqrt_bounds : 1 < Real.sqrt 2 ∧ Real.sqrt 2 < 3 / 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

private theorem α_sq : α ^ 2 = 2 * α + 1 := by
  unfold α
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private theorem β_sq : β ^ 2 = 2 * β + 1 := by
  unfold β
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private def trace : ℕ → ℤ
  | 0 => 2
  | 1 => 2
  | n + 2 => 2 * trace (n + 1) + trace n

private theorem trace_step (j : ℕ) : trace (j + 2) = 2 * trace (j + 1) + trace j := rfl

private theorem trace_eq (j : ℕ) : (trace j : ℝ) = α ^ j + β ^ j := by
  induction j using Nat.twoStepInduction with
  | zero => norm_num [trace]
  | one => simp [trace, α, β]; ring
  | more j h0 h1 =>
    rw [trace_step]
    push_cast
    rw [h0, h1, pow_succ α, pow_succ β, pow_add α j 2, pow_add β j 2, α_sq, β_sq]
    ring

private theorem conjugate_small (j : ℕ) (hj : 2 ≤ j) : 3 * |β ^ j| < 1 := by
  have hneg : β < 0 := by unfold β; linarith [sqrt_bounds.1]
  have habs : |β| ≤ (1 / 2 : ℝ) := by
    rw [abs_of_neg hneg]
    unfold β
    linarith [sqrt_bounds.2]
  have hp : |β ^ j| ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [abs_pow]
    refine (pow_le_pow_left₀ (abs_nonneg _) habs _).trans ?_
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [pow_add]
    exact mul_le_of_le_one_right (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
  nlinarith

private def correction (j : ℕ) : ℤ := if Even j then 1 else 0

private theorem correction_step (j : ℕ) : correction (j + 2) = correction j := by
  simp [correction, Nat.even_add]

private theorem term_eq (j : ℕ) (hj : 2 ≤ j) : term j = 3 * trace j - correction j := by
  have hneg : β < 0 := by unfold β; linarith [sqrt_bounds.1]
  have hsmall := conjugate_small j hj
  have htrace := trace_eq j
  unfold term correction
  by_cases he : Even j
  · rw [if_pos he, Int.floor_eq_iff]
    push_cast
    have hp : 0 < β ^ j := lt_of_le_of_ne (he.pow_nonneg β) (Ne.symm (pow_ne_zero j hneg.ne))
    rw [abs_of_pos hp] at hsmall
    constructor <;> linarith
  · rw [if_neg he, sub_zero, Int.floor_eq_iff]
    push_cast
    have ho : Odd j := Nat.not_even_iff_odd.mp he
    have hp : β ^ j < 0 := ho.pow_neg hneg
    rw [abs_of_neg hp] at hsmall
    constructor <;> linarith

private theorem term_step (j : ℕ) (hj : 2 ≤ j) :
    term (j + 4) - 2 * term (j + 3) - 2 * term (j + 2) + 2 * term (j + 1) + term j = 0 := by
  rw [term_eq _ (by omega), term_eq _ (by omega), term_eq _ (by omega),
    term_eq _ (by omega), term_eq _ hj]
  have hp4 : correction (j + 4) = correction j :=
    (correction_step (j + 2)).trans (correction_step j)
  rw [hp4, correction_step (j + 1), correction_step j]
  linear_combination 3 * trace_step (j + 2) - 3 * trace_step j

private theorem a_step (j : ℕ) : a (j + 1) = a j + term j := by
  simp [a, Finset.sum_range_succ, add_assoc]

private theorem shifted (j : ℕ) (hj : 2 ≤ j) :
    a (j + 5) - 3 * a (j + 4) + 4 * a (j + 2) - a (j + 1) - a j = 0 := by
  linear_combination term_step j hj + a_step (j + 4) - 2 * a_step (j + 3) -
    2 * a_step (j + 2) + 2 * a_step (j + 1) + a_step j

/-- Wu's recurrence, at each index in its stated range. -/
theorem main (n : ℕ) (hn : 6 < n) :
    a n = 3 * a (n - 1) - 4 * a (n - 3) + a (n - 4) + a (n - 5) := by
  have h := shifted (n - 5) (by omega)
  rw [show n - 5 + 5 = n by omega, show n - 5 + 4 = n - 1 by omega,
    show n - 5 + 2 = n - 3 by omega, show n - 5 + 1 = n - 4 by omega] at h
  omega

private theorem alpha_bounds : 2 < α ∧ α < 3 := by
  unfold α
  constructor <;> linarith [sqrt_bounds.1, sqrt_bounds.2]

private theorem negative_one_floor : ⌊3 * α ^ (-1 : ℤ)⌋ = 1 := by
  have hp : 0 < α := by linarith [alpha_bounds.1]
  rw [zpow_neg, zpow_one, ← div_eq_mul_inv, Int.floor_eq_iff]
  norm_num only [Int.cast_one, one_add_one_eq_two]
  constructor
  · rw [le_div_iff₀ hp]
    linarith [alpha_bounds.2]
  · rw [div_lt_iff₀ hp]
    linarith [alpha_bounds.1]

private theorem earlier_floor (j : ℤ) (hj : j ≤ -2) : ⌊3 * α ^ j⌋ = 0 := by
  have hp : 0 < α := by linarith [alpha_bounds.1]
  have hsq : 3 < α ^ 2 := by
    nlinarith [sq_nonneg (α - 2), alpha_bounds.1]
  have hbound : 3 * α ^ (-2 : ℤ) < 1 := by
    rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv, div_lt_iff₀ (pow_pos hp 2), one_mul]
    exact hsq
  have hpow : α ^ j ≤ α ^ (-2 : ℤ) :=
    zpow_le_zpow_right₀ (by linarith [alpha_bounds.1]) hj
  apply Int.floor_eq_iff.mpr
  norm_num only [Int.cast_zero, zero_add]
  exact ⟨mul_nonneg (by norm_num) (zpow_nonneg hp.le j),
    (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans_lt hbound⟩

/-- The finite definition agrees with the floor sum over all positive `k` in OEIS. -/
theorem source (n : ℕ) :
    (∑' k : ℕ, ⌊3 * α ^ ((n : ℤ) - ((k : ℤ) + 1))⌋) = a n := by
  rw [tsum_eq_sum (s := range (n + 1)) (fun k hk => earlier_floor _ (by
    simp only [mem_range, not_lt] at hk
    omega)), sum_range_succ]
  rw [show (n : ℤ) - ((n : ℤ) + 1) = -1 by omega, negative_one_floor]
  unfold a
  rw [add_comm 1]
  congr 1
  calc
    (∑ k ∈ range n, ⌊3 * α ^ ((n : ℤ) - ((k : ℤ) + 1))⌋) =
        ∑ k ∈ range n, term (n - 1 - k) := by
      apply sum_congr rfl
      intro k hk
      have h := mem_range.mp hk
      rw [show (n : ℤ) - ((k : ℤ) + 1) = ((n - 1 - k : ℕ) : ℤ) by omega, zpow_natCast]
      rfl
    _ = _ := sum_range_reflect _ _

private theorem initial_values :
    a 0 = 1 ∧ a 1 = 4 ∧ a 2 = 11 ∧ a 3 = 28 ∧ a 4 = 70 ∧ a 5 = 171 ∧ a 6 = 417 := by
  have t0 : term 0 = 3 := by norm_num [term]
  have t1 : term 1 = 7 := by
    have hlo : (4 / 3 : ℝ) < Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
    rw [term, pow_one, Int.floor_eq_iff]
    norm_num only [Int.cast_ofNat]
    unfold α
    constructor <;> linarith [sqrt_bounds.2]
  have t2 := term_eq 2 (by decide)
  have t3 := term_eq 3 (by decide)
  have t4 := term_eq 4 (by decide)
  have t5 := term_eq 5 (by decide)
  norm_num [trace, correction, Nat.even_iff] at t2 t3 t4 t5
  norm_num [a, sum_range_succ, t0, t1, t2, t3, t4, t5]

open PowerSeries
open scoped PowerSeries

private noncomputable def denominator : ℤ⟦X⟧ := 1 - C 3 * X + C 4 * X ^ 3 - X ^ 4 - X ^ 5

private noncomputable def numerator : ℤ⟦X⟧ := 1 + X - X ^ 2 - X ^ 3 + X ^ 4 + X ^ 6

private theorem generating_product : denominator * mk a = numerator := by
  ext n
  have hshift : coeff n (X * mk a) = if 1 ≤ n then a (n - 1) else 0 := by
    simpa only [pow_one, coeff_mk] using coeff_X_pow_mul' (mk a) 1 n
  simp only [denominator, numerator, sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_C_mul, hshift, coeff_X_pow_mul', coeff_mk, coeff_one, coeff_X, coeff_X_pow]
  by_cases hn : 6 < n
  · have h := main n hn
    simp only [if_pos (by omega : 1 ≤ n), if_pos (by omega : 3 ≤ n),
      if_pos (by omega : 4 ≤ n), if_pos (by omega : 5 ≤ n), if_neg (by omega : n ≠ 0),
      if_neg (by omega : n ≠ 1), if_neg (by omega : n ≠ 2), if_neg (by omega : n ≠ 3),
      if_neg (by omega : n ≠ 4), if_neg (by omega : n ≠ 6)]
    omega
  · obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := initial_values
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [a0, a1, a2, a3, a4, a5, a6]

/-- Wu's generating function with constant term of the denominator normalized to one. -/
theorem generating_function :
    mk a = invOfUnit (1 - C 3 * X + C 4 * X ^ 3 - X ^ 4 - X ^ 5) 1 *
      (1 + X - X ^ 2 - X ^ 3 + X ^ 4 + X ^ 6) := by
  change mk a = invOfUnit denominator 1 * numerator
  have hunit : invOfUnit denominator 1 * denominator = 1 :=
    invOfUnit_mul _ _ (by simp [denominator])
  rw [← generating_product, ← mul_assoc, hunit, one_mul]

end OpenMath.A020964

private theorem sequence_eq : OMA.S_oeis_a020964.a = OpenMath.A020964.a := by
  funext n
  exact OpenMath.A020964.source n

theorem OMA.solution : type_of% @OMA.S_oeis_a020964.main := by
  constructor
  · intro n hn
    simp only [sequence_eq]
    exact OpenMath.A020964.main n hn
  · simp only [sequence_eq]
    exact OpenMath.A020964.generating_function
