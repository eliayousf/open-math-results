import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination

/-! Arie Bos's A003477 identity with the other OEIS sequence A077854.
Both sequences start at index zero. The stated sum misses the constant term. -/

namespace OpenMath.A003477

open PowerSeries Finset
open scoped PowerSeries

private noncomputable def common : ℤ⟦X⟧ := (1 - C 2 * X) * (1 + X ^ 2)
private noncomputable def firstFactor : ℤ⟦X⟧ := 1 - X - C 2 * X ^ 3
private noncomputable def secondFactor : ℤ⟦X⟧ := 1 - X

private noncomputable def firstSeries : ℤ⟦X⟧ := invOfUnit (common * firstFactor) 1
private noncomputable def secondSeries : ℤ⟦X⟧ := invOfUnit (common * secondFactor) 1

/-- A003477 is the coefficient sequence of its OEIS generating function. -/
noncomputable def a (n : ℕ) : ℤ := coeff n firstSeries

/-- A077854 is the coefficient sequence of its OEIS generating function. -/
noncomputable def b (n : ℕ) : ℤ := coeff n secondSeries

private theorem a_zero : a 0 = 1 := by
  simp [a, firstSeries, coeff_zero_eq_constantCoeff_apply]

private theorem series_difference :
    secondFactor * (firstSeries - secondSeries) = C 2 * (X ^ 3 * firstSeries) := by
  have hfirst : common * firstFactor * firstSeries = 1 :=
    mul_invOfUnit _ _ (by simp [common, firstFactor])
  have hsecond : common * secondFactor * secondSeries = 1 :=
    mul_invOfUnit _ _ (by simp [common, secondFactor])
  apply mul_left_cancel₀ (a := common)
  · intro h
    have hc := congrArg (constantCoeff (R := ℤ)) h
    simp [common] at hc
  unfold firstFactor secondFactor at *
  linear_combination hfirst - hsecond

private theorem coefficient_difference (n : ℕ) :
    a n - b n - (if 1 ≤ n then a (n - 1) - b (n - 1) else 0) =
      if 3 ≤ n then 2 * a (n - 3) else 0 := by
  have h := congrArg (coeff (R := ℤ) n) series_difference
  have hshift : coeff n (X * (firstSeries - secondSeries)) =
      if 1 ≤ n then a (n - 1) - b (n - 1) else 0 := by
    simpa only [pow_one, map_sub, a, b] using coeff_X_pow_mul' (firstSeries - secondSeries) 1 n
  dsimp only [a, b] at hshift ⊢
  simp only [secondFactor, sub_mul, one_mul, map_sub, hshift, coeff_C_mul,
    coeff_X_pow_mul'] at h
  exact h.trans (by split_ifs <;> simp)

private theorem difference_two : a 2 - b 2 = 0 := by
  have h₀ := coefficient_difference 0
  have h₁ := coefficient_difference 1
  have h₂ := coefficient_difference 2
  norm_num at h₀ h₁ h₂
  omega

private theorem corrected_shift (m : ℕ) :
    a (m + 3) = b (m + 3) + 2 * (∑ j ∈ range (m + 1), a j) := by
  induction m with
  | zero =>
    have h := coefficient_difference 3
    norm_num at h ⊢
    have hd := difference_two
    omega
  | succ m ih =>
    have h := coefficient_difference (m + 1 + 3)
    rw [if_pos (by omega), if_pos (by omega),
      show m + 1 + 3 - 1 = m + 3 by omega,
      show m + 1 + 3 - 3 = m + 1 by omega] at h
    change a (m + 1 + 3) = b (m + 1 + 3) + 2 * (∑ j ∈ range (m + 1 + 1), a j)
    rw [sum_range_succ]
    omega

/-- The inclusive sum starts with `a 0` and ends with `a (n - 3)`. -/
theorem corrected (n : ℕ) (hn : 3 ≤ n) :
    a n = b n + 2 * (∑ j ∈ range (n - 3 + 1), a j) := by
  simpa only [Nat.sub_add_cancel hn] using corrected_shift (n - 3)

/-- The omission of `a 0 = 1` makes the printed expression too small by two. -/
theorem discrepancy (n : ℕ) (hn : 3 ≤ n) :
    a n = b n + 2 * (∑ j ∈ range (n - 3), a (j + 1)) + 2 := by
  rw [corrected n hn, sum_range_succ', a_zero]
  ring

theorem counterexample_four : a 4 ≠ b 4 + 2 * a 1 := by
  have h := discrepancy 4 (by decide)
  norm_num at h
  omega

/-- The conjecture as printed, on the range where its sum is nonempty, is false. -/
theorem main : ¬ ∀ n : ℕ, 4 ≤ n →
    a n = b n + 2 * (∑ j ∈ range (n - 3), a (j + 1)) := by
  intro h
  have h₄ := h 4 (by decide)
  norm_num at h₄
  exact counterexample_four h₄

end OpenMath.A003477
