import OMAStatements.S_oeis_a289260

namespace OMA.S_oeis_a289260

open PowerSeries
open scoped PowerSeries

private noncomputable def numerator : ℤ⟦X⟧ := 1 + X + X ^ 5 + X ^ 6

private noncomputable def kernel : ℤ⟦X⟧ := 1 - X - X ^ 3 - X ^ 3

private noncomputable def differences : ℤ⟦X⟧ := (1 - X) * generatingSeries

private theorem coeff_shift_one (f : ℤ⟦X⟧) (n : ℕ) :
    coeff n (X * f) = if 1 ≤ n then coeff (n - 1) f else 0 := by
  simpa only [pow_one] using coeff_X_pow_mul' f 1 n

private theorem floor_shift (n : ℕ) :
    signedFloor (n + 5) + signedFloor n = 8 * (-1 : ℤ) ^ (n + 5) := by
  have hd : 8 * (n + 5 + 1) / 5 = 8 * (n + 1) / 5 + 8 := by omega
  simp only [signedFloor, hd, Nat.cast_add, Nat.cast_ofNat, pow_add]
  ring

private theorem floor_cancel (n : ℕ) :
    signedFloor (n + 6) + signedFloor (n + 5) + signedFloor (n + 1) + signedFloor n = 0 := by
  have h := floor_shift (n + 1)
  have h' := floor_shift n
  rw [show n + 1 + 5 = n + 6 by omega] at h
  simp only [pow_add] at h h'
  linear_combination h + h'

private theorem denominator_identity : numerator * denominator = (1 - X) * kernel := by
  have hexpand : (1 - X) * kernel =
      (1 : ℤ⟦X⟧) - X - X + X ^ 2 - X ^ 3 - X ^ 3 + X ^ 4 + X ^ 4 := by
    unfold kernel
    ring
  rw [hexpand]
  apply PowerSeries.ext
  intro n
  simp only [numerator, add_mul, one_mul, map_add, map_sub, coeff_shift_one,
    coeff_X_pow_mul', denominator, coeff_mk, coeff_one, coeff_X, coeff_X_pow]
  by_cases hn : n < 6
  · have hsmall : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hsmall with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [signedFloor]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 6 := ⟨n - 6, by omega⟩
    simp only [if_pos (show 1 ≤ k + 6 by omega), if_pos (show 5 ≤ k + 6 by omega),
      if_pos (show 6 ≤ k + 6 by omega), if_neg (show k + 6 ≠ 0 by omega),
      if_neg (show k + 6 ≠ 1 by omega), if_neg (show k + 6 ≠ 2 by omega),
      if_neg (show k + 6 ≠ 3 by omega), if_neg (show k + 6 ≠ 4 by omega),
      show k + 6 - 1 = k + 5 by omega, show k + 6 - 5 = k + 1 by omega,
      show k + 6 - 6 = k by omega, zero_sub, neg_zero, zero_add]
    exact floor_cancel k

private theorem kernel_identity : kernel * differences = numerator := by
  have hinverse : denominator * generatingSeries = 1 := by
    unfold generatingSeries
    apply mul_invOfUnit
    norm_num [denominator, signedFloor]
  calc
    kernel * differences = ((1 - X) * kernel) * generatingSeries := by
      unfold differences
      ring
    _ = (numerator * denominator) * generatingSeries := by rw [denominator_identity]
    _ = numerator := by rw [mul_assoc, hinverse, mul_one]

private theorem numerator_nonneg (n : ℕ) : 0 ≤ coeff n numerator := by
  simp only [numerator, map_add, coeff_one, coeff_X, coeff_X_pow]
  split_ifs <;> norm_num

private theorem differences_pos (n : ℕ) : 0 < coeff n differences := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hr := congrArg (coeff n) kernel_identity
    simp only [kernel, sub_mul, one_mul, map_sub, coeff_shift_one, coeff_X_pow_mul'] at hr
    by_cases hn : n = 0
    · subst n
      have hzero : coeff 0 differences = 1 := by
        simpa [numerator, coeff_one, coeff_X, coeff_X_pow] using hr
      rw [hzero]
      decide
    · have hprev := ih (n - 1) (by omega)
      have hnum := numerator_nonneg n
      rw [if_pos (show 1 ≤ n by omega)] at hr
      by_cases h3 : 3 ≤ n
      · rw [if_pos h3] at hr
        have hthird := ih (n - 3) (by omega)
        omega
      · rw [if_neg h3] at hr
        omega

end OMA.S_oeis_a289260

open PowerSeries OMA.S_oeis_a289260 in
theorem OMA.solution : type_of% @OMA.S_oeis_a289260.main := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := differences_pos (n + 1)
  simp only [differences, sub_mul, one_mul, map_sub, coeff_shift_one, Nat.add_sub_cancel] at h
  exact sub_pos.mp h
