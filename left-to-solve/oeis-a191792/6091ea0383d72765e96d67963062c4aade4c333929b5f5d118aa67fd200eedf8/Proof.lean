import OMAStatements.S_oeis_a191792
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OpenMath.A191792

open PowerSeries
open OMA.S_oeis_a191792 (K T radical B a)

private noncomputable def A : PowerSeries ℚ := mk a

private theorem radicalSubst : HasSubst (-(2 * X ^ 2) - 5 * X ^ 4 - 2 * X ^ 6 + X ^ 8 : PowerSeries ℚ) := by
  apply HasSubst.of_constantCoeff_zero'
  simp

private theorem radicalSquare : radical ^ 2 = K * T := by
  have hs : (binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = 1 + X := by
    rw [pow_two, ← binomialSeries_add]
    have hn : (1 / 2 : ℚ) + 1 / 2 = (↑(1 : ℕ) : ℚ) := by norm_num
    rw [hn, binomialSeries_nat, pow_one]
  unfold radical K T
  rw [← subst_pow radicalSubst, hs, subst_add radicalSubst, subst_X radicalSubst,
    ← coe_substAlgHom radicalSubst, map_one]
  ring

private theorem constB : constantCoeff B = 1 := by
  have hr : constantCoeff radical = 1 := by
    unfold radical
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' radicalSubst, finsum_eq_single _ 0]
    · simp
    · intro j hj
      have h0 : constantCoeff (-(2 * X ^ 2) - 5 * X ^ 4 - 2 * X ^ 6 + X ^ 8 : PowerSeries ℚ) = 0 := by simp
      simp only [coeff_zero_eq_constantCoeff_apply, map_pow, h0, zero_pow hj, smul_zero]
  simp [B, K, hr, constantCoeff_inv]

private theorem KB : K * B = radical := by
  have h : K * K⁻¹ = 1 := by apply PowerSeries.mul_inv_cancel; simp [K]
  change K * (radical * K⁻¹) = radical
  calc
    K * (radical * K⁻¹) = radical * (K * K⁻¹) := by ring
    _ = radical := by rw [h, mul_one]

private theorem equationB : K * B ^ 2 = T := by
  have hK : K ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [K] at h'
  have h := radicalSquare
  rw [← KB] at h
  exact mul_left_cancel₀ hK (by linear_combination h)

private theorem d_two : derivative ℚ (2 : PowerSeries ℚ) = 0 := (derivative ℚ).map_natCast 2

private theorem derivativeK : derivative ℚ K = -2 + 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by
  unfold K
  simp only [map_add, map_sub, Derivation.leibniz, smul_eq_mul, derivative_one, derivative_X,
    derivative_pow, d_two]
  norm_num
  ring

private theorem derivativeT : derivative ℚ T = 2 + 2 * X + 6 * X ^ 2 + 4 * X ^ 3 := by
  unfold T
  simp only [map_add, Derivation.leibniz, smul_eq_mul, derivative_one, derivative_X,
    derivative_pow, d_two]
  norm_num
  ring

private theorem derivativeB :
    2 * (K * T) * derivative ℚ B = (K * derivative ℚ T - derivative ℚ K * T) * B := by
  have hB : B ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [constB] at h'
  have h := congrArg (derivative ℚ) equationB
  simp only [Derivation.leibniz, smul_eq_mul, derivative_pow] at h
  norm_num at h
  apply mul_left_cancel₀ hB
  linear_combination (K * B ^ 2) * h -
    (2 * K * B * derivative ℚ B + derivative ℚ K * B ^ 2) * equationB

private theorem B_from_A : B = 1 + 2 * X * A := by
  have h : (2 : PowerSeries ℚ) = C (2 : ℚ) := (map_natCast C 2).symm
  have hshift : 2 * X * A = C (2 : ℚ) * (A * X ^ 1) := by rw [← h]; ring
  have heq : 2 * X * A = B - 1 := by
    rw [hshift]
    ext n
    rw [coeff_C_mul, coeff_mul_X_pow']
    cases n with
    | zero => simp [coeff_zero_eq_constantCoeff_apply, constB]
    | succ n =>
      rw [if_pos (by omega), Nat.succ_sub_one, A, coeff_mk, a]
      ring
  linear_combination -heq

private theorem derivativeB_from_A : derivative ℚ B = 2 * A + 2 * X * derivative ℚ A := by
  rw [B_from_A]
  simp only [map_add, derivative_one, derivative_X, Derivation.leibniz,
    smul_eq_mul, d_two, mul_zero, add_zero, mul_one, zero_add]
  ring

private theorem ode :
    X * (1 - 2 * X ^ 2 - 5 * X ^ 4 - 2 * X ^ 6 + X ^ 8) * derivative ℚ A +
      (1 - 2 * X - 2 * X ^ 2 - 4 * X ^ 3 - 5 * X ^ 4 + 4 * X ^ 5 -
        2 * X ^ 6 + 2 * X ^ 7 + X ^ 8) * A = 1 + 2 * X ^ 2 - 2 * X ^ 4 - X ^ 6 := by
  have h := derivativeB
  rw [derivativeK, derivativeT, derivativeB_from_A, B_from_A] at h
  unfold K T at h
  have h4 : (4 : PowerSeries ℚ) ≠ 0 := by
    intro hh
    have hc : constantCoeff (4 : PowerSeries ℚ) = (4 : ℚ) := map_natCast constantCoeff 4
    have eq := congrArg constantCoeff hh
    rw [hc, map_zero] at eq
    norm_num at eq
  apply mul_left_cancel₀ h4
  linear_combination h

private theorem odeExpanded :
    derivative ℚ A * X ^ 1 - C (2 : ℚ) * (derivative ℚ A * X ^ 3) -
    C (5 : ℚ) * (derivative ℚ A * X ^ 5) - C (2 : ℚ) * (derivative ℚ A * X ^ 7) +
    derivative ℚ A * X ^ 9 + A - C (2 : ℚ) * (A * X ^ 1) - C (2 : ℚ) * (A * X ^ 2) -
    C (4 : ℚ) * (A * X ^ 3) - C (5 : ℚ) * (A * X ^ 4) + C (4 : ℚ) * (A * X ^ 5) -
    C (2 : ℚ) * (A * X ^ 6) + C (2 : ℚ) * (A * X ^ 7) + A * X ^ 8 =
    1 + C (2 : ℚ) * X ^ 2 - C (2 : ℚ) * X ^ 4 - X ^ 6 := by
  rw [show C (2 : ℚ) = (2 : PowerSeries ℚ) from map_natCast C 2,
      show C (4 : ℚ) = (4 : PowerSeries ℚ) from map_natCast C 4,
      show C (5 : ℚ) = (5 : PowerSeries ℚ) from map_natCast C 5]
  linear_combination ode

theorem main (n : ℕ) (hn : 8 ≤ n) :
    ((n : ℚ) + 1) * a n - 2 * a (n - 1) + 2 * (-(n : ℚ) + 1) * a (n - 2) -
      4 * a (n - 3) + 5 * (-(n : ℚ) + 3) * a (n - 4) + 4 * a (n - 5) +
      2 * (-(n : ℚ) + 5) * a (n - 6) + 2 * a (n - 7) + ((n : ℚ) - 7) * a (n - 8) = 0 := by
  have h := congrArg (coeff n) odeExpanded
  have hd9 : coeff n (derivative ℚ A * X ^ 9) = ((n : ℚ) - 8) * a (n - 8) := by
    rw [coeff_mul_X_pow']
    split_ifs with h9
    · have hcast := congrArg (fun k : ℕ => (k : ℚ)) (show n - 9 + 1 = n - 8 by omega)
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hn] at hcast
      rw [coeff_derivative, hcast, show n - 9 + 1 = n - 8 by omega, mul_comm]
      simp [A]
    · have : n = 8 := by omega
      subst n
      norm_num
  have hc0 : coeff n (1 : PowerSeries ℚ) = 0 := by simp [coeff_one, show n ≠ 0 by omega]
  have hc2 : coeff n (X ^ 2 : PowerSeries ℚ) = 0 := by simp [coeff_X_pow, show n ≠ 2 by omega]
  have hc4 : coeff n (X ^ 4 : PowerSeries ℚ) = 0 := by simp [coeff_X_pow, show n ≠ 4 by omega]
  have hc6 : coeff n (X ^ 6 : PowerSeries ℚ) = 0 := by simp [coeff_X_pow, show n ≠ 6 by omega]
  simp only [map_add, map_sub, coeff_C_mul, hd9] at h
  simp only [coeff_mul_X_pow',
    if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega),
    if_pos (show 4 ≤ n by omega), if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega),
    if_pos (show 7 ≤ n by omega), if_pos hn, coeff_derivative, A, coeff_mk,
    show n - 1 + 1 = n by omega, show n - 3 + 1 = n - 2 by omega,
    show n - 5 + 1 = n - 4 by omega, show n - 7 + 1 = n - 6 by omega,
    Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega),
    Nat.cast_sub (show 5 ≤ n by omega), Nat.cast_sub (show 7 ≤ n by omega),
    Nat.cast_ofNat, hc0, hc2, hc4, hc6] at h
  linear_combination h

end OpenMath.A191792

theorem OMA.solution : type_of% @OMA.S_oeis_a191792.main := OpenMath.A191792.main
