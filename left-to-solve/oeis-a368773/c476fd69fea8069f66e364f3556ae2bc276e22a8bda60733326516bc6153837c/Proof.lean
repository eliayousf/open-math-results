import OMAStatements.S_oeis_a368773
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OpenMath.A368773

open PowerSeries
open OMA.S_oeis_a368773 (radical B a)

private noncomputable def A : PowerSeries ℚ := mk a
private noncomputable def K : PowerSeries ℚ := 1 - 3 * X
private noncomputable def T : PowerSeries ℚ := (1 + 3 * X) * (1 - X ^ 2)

private theorem radicalSubst : HasSubst (-10 * X ^ 2 + 9 * X ^ 4 : PowerSeries ℚ) := by
  apply HasSubst.of_constantCoeff_zero'
  simp

private theorem radicalSquare : radical ^ 2 = 1 - 10 * X ^ 2 + 9 * X ^ 4 := by
  have hs : (binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = 1 + X := by
    rw [pow_two, ← binomialSeries_add]
    have hn : (1 / 2 : ℚ) + 1 / 2 = (↑(1 : ℕ) : ℚ) := by norm_num
    rw [hn, binomialSeries_nat, pow_one]
  unfold radical
  rw [← subst_pow radicalSubst, hs, subst_add radicalSubst, subst_X radicalSubst,
    ← coe_substAlgHom radicalSubst, map_one]
  ring

private theorem constB : constantCoeff B = 1 := by
  have hr : constantCoeff radical = 1 := by
    unfold radical
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' radicalSubst, finsum_eq_single _ 0]
    · simp
    · intro j hj
      have h0 : constantCoeff (-10 * X ^ 2 + 9 * X ^ 4 : PowerSeries ℚ) = 0 := by simp
      simp only [coeff_zero_eq_constantCoeff_apply, map_pow, h0, zero_pow hj, smul_zero]
  simp [B, hr, constantCoeff_inv]

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
  apply mul_left_cancel₀ hK
  unfold K at h
  unfold K T
  linear_combination h

private theorem derivativeK : derivative ℚ K = -3 := by
  have d3 : derivative ℚ (3 : PowerSeries ℚ) = 0 := (derivative ℚ).map_natCast 3
  simp [K, d3, smul_eq_mul]

private theorem derivativeT : derivative ℚ T = 3 - 2 * X - 9 * X ^ 2 := by
  have d3 : derivative ℚ (3 : PowerSeries ℚ) = 0 := (derivative ℚ).map_natCast 3
  unfold T
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_sub, d3, derivative_one,
    derivative_X, derivative_pow]
  norm_num
  ring

private theorem derivativeB :
    2 * (K * T) * derivative ℚ B = (K * derivative ℚ T + 3 * T) * B := by
  have hB : B ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [constB] at h'
  have h := congrArg (derivative ℚ) equationB
  simp only [Derivation.leibniz, smul_eq_mul, derivativeK, derivative_pow] at h
  norm_num at h
  apply mul_left_cancel₀ hB
  linear_combination (K * B ^ 2) * h - (2 * K * B * derivative ℚ B - 3 * B ^ 2) * equationB

private theorem B_from_A : B = 1 - X + 4 * X * A := by
  have h : (4 : PowerSeries ℚ) = C (4 : ℚ) := (map_natCast C 4).symm
  have hshift : 4 * X * A = C (4 : ℚ) * (A * X ^ 1) := by rw [← h]; ring
  have heq : 4 * X * A = B - 1 + X := by
    rw [hshift]
    ext n
    rw [coeff_C_mul, coeff_mul_X_pow']
    cases n with
    | zero => simp [coeff_zero_eq_constantCoeff_apply, constB]
    | succ n =>
      rw [if_pos (by omega), Nat.succ_sub_one]
      rw [A, coeff_mk, a]
      ring
  linear_combination -heq

private theorem derivativeB_from_A : derivative ℚ B = -1 + 4 * A + 4 * X * derivative ℚ A := by
  have d4 : derivative ℚ (4 : PowerSeries ℚ) = 0 := (derivative ℚ).map_natCast 4
  rw [B_from_A]
  simp only [map_add, map_sub, derivative_one, derivative_X, Derivation.leibniz,
    smul_eq_mul, d4, mul_zero, add_zero, mul_one, zero_sub]
  ring

private theorem ode :
    X * (1 - 10 * X ^ 2 + 9 * X ^ 4) * derivative ℚ A +
      (1 - 3 * X - 9 * X ^ 2 + 3 * X ^ 3) * A = 1 - X - 3 * X ^ 2 + 3 * X ^ 3 := by
  have h := derivativeB
  rw [derivativeT, derivativeB_from_A, B_from_A] at h
  unfold K T at h
  have h8 : (8 : PowerSeries ℚ) ≠ 0 := by
    intro hh
    have hc : constantCoeff (8 : PowerSeries ℚ) = (8 : ℚ) := map_natCast constantCoeff 8
    have eq := congrArg constantCoeff hh
    rw [hc, map_zero] at eq
    norm_num at eq
  apply mul_left_cancel₀ h8
  linear_combination h

private theorem odeExpanded :
    derivative ℚ A * X ^ 1 - C (10 : ℚ) * (derivative ℚ A * X ^ 3) +
    C (9 : ℚ) * (derivative ℚ A * X ^ 5) + A - C (3 : ℚ) * (A * X ^ 1) -
    C (9 : ℚ) * (A * X ^ 2) + C (3 : ℚ) * (A * X ^ 3) =
    1 - X - C (3 : ℚ) * X ^ 2 + C (3 : ℚ) * X ^ 3 := by
  rw [show C (10 : ℚ) = (10 : PowerSeries ℚ) from map_natCast C 10,
      show C (9 : ℚ) = (9 : PowerSeries ℚ) from map_natCast C 9,
      show C (3 : ℚ) = (3 : PowerSeries ℚ) from map_natCast C 3]
  linear_combination ode

theorem main (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℚ) + 1) * a n - 3 * a (n - 1) + (-(10 : ℚ) * n + 11) * a (n - 2) +
      3 * a (n - 3) + 9 * ((n : ℚ) - 4) * a (n - 4) = 0 := by
  have h := congrArg (coeff n) odeExpanded
  have hd5 : coeff n (derivative ℚ A * X ^ 5) = ((n : ℚ) - 4) * a (n - 4) := by
    rw [coeff_mul_X_pow']
    split_ifs with h5
    · have hcast := congrArg (fun k : ℕ => (k : ℚ)) (show n - 5 + 1 = n - 4 by omega)
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hn] at hcast
      rw [coeff_derivative, hcast, show n - 5 + 1 = n - 4 by omega, mul_comm]
      simp [A]
    · have : n = 4 := by omega
      subst n
      norm_num
  have hc0 : coeff n (1 : PowerSeries ℚ) = 0 := by simp [coeff_one, show n ≠ 0 by omega]
  have hc1 : coeff n (X : PowerSeries ℚ) = 0 := by simp [coeff_X, show n ≠ 1 by omega]
  have hc2 : coeff n (X ^ 2 : PowerSeries ℚ) = 0 := by simp [coeff_X_pow, show n ≠ 2 by omega]
  have hc3 : coeff n (X ^ 3 : PowerSeries ℚ) = 0 := by simp [coeff_X_pow, show n ≠ 3 by omega]
  simp only [map_add, map_sub, coeff_C_mul, hd5] at h
  simp only [coeff_mul_X_pow',
    if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega),
    coeff_derivative, A, coeff_mk, show n - 1 + 1 = n by omega,
    show n - 3 + 1 = n - 2 by omega, Nat.cast_sub (show 1 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_ofNat, hc0, hc1, hc2, hc3] at h
  linear_combination h

end OpenMath.A368773

theorem OMA.solution : type_of% @OMA.S_oeis_a368773.main := OpenMath.A368773.main
