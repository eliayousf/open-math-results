import OMAStatements.S_oeis_a320097
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

open Finset Matrix

namespace OpenMath.A320097

open OMA.S_oeis_a320097

private theorem state_succ (n : ℕ) : state (n+1) = transfer *ᵥ state n := rfl

private def entries : Matrix (Fin 16) (Fin 16) ℤ :=
    !![1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2;
    0, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3;
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2;
    1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4;
    0, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2;
    1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 2, 3;
    1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2;
    1, 2, 1, 2, 2, 3, 2, 4, 2, 3, 2, 4, 2, 3, 2, 4;
    0, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3;
    1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 5;
    1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 3, 3;
    1, 2, 1, 2, 2, 3, 2, 4, 2, 3, 2, 4, 3, 5, 3, 6;
    1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 4;
    1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 5, 2, 4, 4, 6;
    1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 3, 3, 2, 4, 4, 4;
    2, 3, 2, 4, 2, 3, 2, 4, 3, 5, 3, 6, 4, 6, 4, 8]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private theorem entries_match : entries = transfer := by
  decide +kernel

private def table : Fin 8 → Fin 16 → ℤ :=
    !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2;
    15, 20, 16, 28, 16, 28, 23, 36, 20, 35, 28, 44, 28, 44, 36, 59;
    463, 739, 600, 976, 600, 976, 809, 1306, 739, 1202, 976, 1576, 976, 1576, 1306, 2115;
    16372, 26466, 21469, 34750, 21469, 34750, 28777, 46555, 26466, 42838, 34750, 56219, 34750, 56219, 46555, 75332;
    583199, 943577, 765471, 1238588, 765471, 1238588, 1025732, 1659652, 943577, 1526776, 1238588, 2004059, 1238588, 2004059, 1659652, 2685384;
    20788249, 33635952, 27286857, 44151134, 27286857, 44151134, 36563451, 59160865, 33635952, 54424201, 44151134, 71437991, 44151134, 71437991, 59160865, 95724316;
    741026781, 1199006178, 972683006, 1573834337, 972683006, 1573834337, 1303360031, 2108880730, 1199006178, 1940032959, 1573834337, 2546517343, 1573834337, 2546517343, 2108880730, 3412240761]

private theorem table_initial : state 0 = table 0 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private theorem table_step : ∀ j : Fin 7, entries *ᵥ table j.castSucc = table j.succ := by
  decide +kernel

private theorem table_match (n : ℕ) (hn : n ≤ 7) :
    state n = table ⟨n, by omega⟩ := by
  induction n with
  | zero => exact table_initial
  | succ n ih =>
    rw [state_succ, ih (by omega), ← entries_match]
    exact table_step ⟨n,by omega⟩

private theorem base_vec :
    table 7 = (36 : ℤ) • table 6 - (7 : ℤ) • table 5 - (201 : ℤ) • table 4
      + (49 : ℤ) • table 3 + (20 : ℤ) • table 2 - (5 : ℤ) • table 1 := by decide +kernel

private theorem state_recurrence (k : ℕ) :
    state (k + 7) = (36 : ℤ) • state (k + 6) - (7 : ℤ) • state (k + 5) - (201 : ℤ) • state (k + 4)
      + (49 : ℤ) • state (k + 3) + (20 : ℤ) • state (k + 2) - (5 : ℤ) • state (k + 1) := by
  induction k with
  | zero =>
    simp only [Nat.zero_add]
    rw [table_match 7 (by omega), table_match 6 (by omega), table_match 5 (by omega), table_match 4 (by omega), table_match 3 (by omega), table_match 2 (by omega), table_match 1 (by omega)]
    exact base_vec
  | succ k ih =>
    have h := congrArg (fun v : Fin 16 → ℤ => transfer *ᵥ v) ih
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
      ← state_succ] at h
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem recurrence (n : ℕ) (hn : 7 ≤ n) :
    a n = 36 * a (n - 1) - 7 * a (n - 2) - 201 * a (n - 3)
      + 49 * a (n - 4) + 20 * a (n - 5) - 5 * a (n - 6) := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, n = k + 7 := ⟨n - 7, by omega⟩
  rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega, show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega, show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega]
  have hh := congrFun (state_recurrence k) (0 : Fin 16)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at hh
  simpa [a, zsmul_eq_mul] using hh

private theorem count_table (n : ℕ) (hn : n ≤ 7) : a n = table ⟨n,by omega⟩ 0 :=
  congrFun (table_match n hn) 0

open PowerSeries in
theorem generating_function :
    (1 - C 36 * X ^ 1 + C 7 * X ^ 2 + C 201 * X ^ 3 -
      C 49 * X ^ 4 - C 20 * X ^ 5 + C 5 * X ^ 6 : ℤ⟦X⟧) * mk series =
      X ^ 1 - C 21 * X ^ 2 - C 70 * X ^ 3 + C 10 * X ^ 4 + C 14 * X ^ 5 - C 3 * X ^ 6 := by
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n < 7
  · interval_cases n <;> norm_num [series, count_table, table]
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega),
      if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega),
      series, if_neg (show n ≠ 0 by omega), if_neg (show n - 1 ≠ 0 by omega),
      if_neg (show n - 2 ≠ 0 by omega), if_neg (show n - 3 ≠ 0 by omega),
      if_neg (show n - 4 ≠ 0 by omega), if_neg (show n - 5 ≠ 0 by omega),
      if_neg (show n - 6 ≠ 0 by omega)]
    have h := recurrence n (by omega)
    omega

end OpenMath.A320097

theorem OMA.solution : type_of% @OMA.S_oeis_a320097.main :=
  ⟨OpenMath.A320097.recurrence, OpenMath.A320097.generating_function⟩
