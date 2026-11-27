import OMAStatements.S_oeis_a351933
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace OpenMath.A351933

open PowerSeries
open OMA.S_oeis_a351933 (denominator argument series a)

private theorem den_arg : denominator * argument = 2 * X := by
  have h : denominator * denominator⁻¹ = 1 := by
    apply PowerSeries.mul_inv_cancel
    have hc : constantCoeff (2 : PowerSeries ℚ) = (2 : ℚ) :=
      map_natCast constantCoeff 2
    norm_num [denominator, hc]
  unfold argument
  calc
    denominator * (2 * X * denominator⁻¹) = 2 * X * (denominator * denominator⁻¹) := by ring
    _ = 2 * X := by rw [h, mul_one]

private theorem d_two : derivative ℚ (2 : PowerSeries ℚ) = 0 :=
  (derivative ℚ).map_natCast 2

private theorem d_denom : derivative ℚ denominator = -2 * X := by
  rw [denominator, map_sub, d_two, derivative_pow]
  norm_num

private theorem d_argument : denominator ^ 2 * derivative ℚ argument = 4 + 2 * X ^ 2 := by
  have h := congrArg (derivative ℚ) den_arg
  simp only [Derivation.leibniz, smul_eq_mul, d_denom, derivative_X,
    d_two, mul_zero, mul_one] at h
  have harg := den_arg
  unfold denominator at h harg ⊢
  linear_combination (2 - X ^ 2) * h + 2 * X * harg

private theorem ode : denominator ^ 2 * derivative ℚ series = (4 + 2 * X ^ 2) * series := by
  have ha : HasSubst argument := by
    apply HasSubst.of_constantCoeff_zero'
    simp [argument]
  unfold series
  rw [derivative_subst ha, derivative_exp]
  linear_combination (PowerSeries.exp ℚ).subst argument * d_argument

private theorem odeExpanded :
    C (4 : ℚ) * derivative ℚ series - C (4 : ℚ) * (derivative ℚ series * X ^ 2) +
      derivative ℚ series * X ^ 4 = C (4 : ℚ) * series + C (2 : ℚ) * (series * X ^ 2) := by
  have hc4 : C (4 : ℚ) = (4 : PowerSeries ℚ) := map_natCast C 4
  have hc2 : C (2 : ℚ) = (2 : PowerSeries ℚ) := map_natCast C 2
  rw [hc4, hc2]
  have h := ode
  unfold denominator at h
  linear_combination h

private theorem coefficientEquation (t : ℕ) :
    4 * (↑t + 4) * coeff (t+4) series - 4 * (↑t + 2) * coeff (t+2) series +
      ↑t * coeff t series = 4 * coeff (t+3) series + 2 * coeff (t+1) series := by
  have h := congrArg (coeff (t+3)) odeExpanded
  have h4 : coeff (t+3) (derivative ℚ series * X ^ 4) = (t : ℚ) * coeff t series := by
    rw [coeff_mul_X_pow']
    split_ifs with h4
    · have ht := congrArg (fun n : ℕ => (n : ℚ)) (show t + 3 - 4 + 1 = t by omega)
      rw [Nat.cast_add, Nat.cast_one] at ht
      rw [coeff_derivative, ht, show t + 3 - 4 + 1 = t by omega, mul_comm]
    · have ht : t = 0 := by omega
      simp [ht]
  simp only [map_add, map_sub, coeff_C_mul, h4, coeff_mul_X_pow',
    if_pos (show 2 ≤ t + 3 by omega), coeff_derivative,
    show t + 3 - 2 = t+1 by omega, Nat.cast_add, Nat.cast_ofNat] at h
  linear_combination h

theorem main (n : ℕ) (hn : 4 ≤ n) :
    4 * a n - 4 * a (n - 1) - 4 * ((n : ℚ) - 1) * ((n : ℚ) - 2) * a (n - 2) -
      2 * ((n : ℚ) - 1) * ((n : ℚ) - 2) * a (n - 3) +
      ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) * a (n - 4) = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 4 t, show t + 4 - 1 = t + 3 by omega,
    show t + 4 - 2 = t + 2 by omega, show t + 4 - 3 = t + 1 by omega,
    show t + 4 - 4 = t by omega]
  simp only [a, Nat.cast_add, Nat.cast_ofNat, Nat.factorial_succ, Nat.cast_mul]
  linear_combination ((t.factorial : ℚ) * (t+1) * (t+2) * (t+3)) * coefficientEquation t

end OpenMath.A351933

theorem OMA.solution : type_of% @OMA.S_oeis_a351933.main := OpenMath.A351933.main
