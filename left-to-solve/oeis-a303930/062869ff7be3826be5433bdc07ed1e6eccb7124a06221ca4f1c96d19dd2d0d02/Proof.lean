import OMAStatements.S_oeis_a303930
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Finset Matrix PowerSeries

namespace OpenMath.A303930

open OMA.S_oeis_a303930

private def entries : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1,0,0,1; 0,1,1,1; 0,1,1,1; 1,1,1,2]

private theorem entries_eq : entries = transfer := by decide +kernel

private theorem vector_step (n : ℕ) : v (n+1) = transfer *ᵥ v n := rfl

private theorem vector_rec (k : ℕ) :
    v (k+3) = (5 : ℤ) • v (k+2) - (5 : ℤ) • v (k+1) := by
  induction k with
  | zero =>
    simp only [Nat.zero_add]
    simp only [vector_step, ← entries_eq]
    decide +kernel
  | succ k ih =>
    have h := congrArg (fun z : Fin 4 → ℤ => transfer *ᵥ z) ih
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, ← vector_step] at h
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem unrestr_rec (k : ℕ) :
    unrestricted (k+3) = 5 * unrestricted (k+2) - 5 * unrestricted (k+1) := by
  have h := congrFun (vector_rec k) (0 : Fin 4)
  simp only [Pi.sub_apply,Pi.smul_apply] at h
  simpa [unrestricted,zsmul_eq_mul] using h

private theorem horiz_rec (k : ℕ) :
    horizontal (k+2) = 3 * horizontal (k+1) - horizontal k := by
  simp only [horizontal, symmetricState]
  omega

private theorem refl_rec (k : ℕ) :
    reflected (k+5) = 5 * reflected (k+3) - 5 * reflected (k+1) := by
  by_cases h : k = 0
  · subst k
    simp only [Nat.zero_add, reflected, vector_step, ← entries_eq]
    decide +kernel
  · let j := (k+5)/2 - 3
    have hv := vector_rec j
    have ha : j + 3 = (k+5)/2 := by omega
    have hb : j + 2 = (k+3)/2 := by omega
    have hc : j + 1 = (k+1)/2 := by omega
    rw [ha,hb,hc] at hv
    have h0 := congrFun hv (0 : Fin 4)
    have h1 := congrFun hv (1 : Fin 4)
    have h2 := congrFun hv (2 : Fin 4)
    have h3 := congrFun hv (3 : Fin 4)
    simp only [Pi.sub_apply,Pi.smul_apply] at h0 h1 h2 h3
    simp at h0 h1 h2 h3
    simp only [reflected, show (k+5)%2 = (k+1)%2 by omega,
      show (k+3)%2 = (k+1)%2 by omega]
    by_cases hp : (k+1)%2=0
    · simp only [if_pos hp]
      omega
    · simp only [if_neg hp]
      omega

private theorem unrestricted_residual (k : ℕ) :
    unrestricted (k+9) - 8 * unrestricted (k+8) + 16 * unrestricted (k+7) + 20 * unrestricted (k+6) - 95 * unrestricted (k+5) + 60 * unrestricted (k+4) + 80 * unrestricted (k+3) - 100 * unrestricted (k+2) + 25 * unrestricted (k+1) = 0 := by
  have h0 := unrestr_rec (k+6)
  have h1 := unrestr_rec (k+5)
  have h2 := unrestr_rec (k+4)
  have h3 := unrestr_rec (k+3)
  have h5 := unrestr_rec (k+1)
  have h6 := unrestr_rec (k+0)
  simp only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero] at h0 h1 h2 h3 h5 h6
  omega

private theorem horizontal_residual (k : ℕ) :
    horizontal (k+9) - 8 * horizontal (k+8) + 16 * horizontal (k+7) + 20 * horizontal (k+6) - 95 * horizontal (k+5) + 60 * horizontal (k+4) + 80 * horizontal (k+3) - 100 * horizontal (k+2) + 25 * horizontal (k+1) = 0 := by
  have h0 := horiz_rec (k+7)
  have h1 := horiz_rec (k+6)
  have h3 := horiz_rec (k+4)
  have h4 := horiz_rec (k+3)
  have h5 := horiz_rec (k+2)
  have h6 := horiz_rec (k+1)
  simp only [Nat.add_assoc,Nat.reduceAdd] at h0 h1 h3 h4 h5 h6
  omega

private theorem reflected_residual (k : ℕ) :
    reflected (k+9) - 8 * reflected (k+8) + 16 * reflected (k+7) + 20 * reflected (k+6) - 95 * reflected (k+5) + 60 * reflected (k+4) + 80 * reflected (k+3) - 100 * reflected (k+2) + 25 * reflected (k+1) = 0 := by
  have h0 := refl_rec (k+4)
  have h1 := refl_rec (k+3)
  have h2 := refl_rec (k+2)
  have h3 := refl_rec (k+1)
  have h4 := refl_rec (k+0)
  simp only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero] at h0 h1 h2 h3 h4
  omega

private theorem numerator_residual (k : ℕ) :
    numerator (k+9) - 8 * numerator (k+8) + 16 * numerator (k+7) + 20 * numerator (k+6) - 95 * numerator (k+5) + 60 * numerator (k+4) + 80 * numerator (k+3) - 100 * numerator (k+2) + 25 * numerator (k+1) = 0 := by
  have h0 := unrestricted_residual k
  have h1 := horizontal_residual k
  have h2 := reflected_residual k
  unfold numerator
  omega

theorem recurrence (n : ℕ) (hn : 9 ≤ n) :
    a n = 8 * a (n-1) - 16 * a (n-2) - 20 * a (n-3) + 95 * a (n-4) - 60 * a (n-5) - 80 * a (n-6) + 100 * a (n-7) - 25 * a (n-8) := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, n = k+9 := ⟨n-9, by omega⟩
  rw [show k+9-1=k+8 by omega, show k+9-2=k+7 by omega, show k+9-3=k+6 by omega, show k+9-4=k+5 by omega, show k+9-5=k+4 by omega, show k+9-6=k+3 by omega, show k+9-7=k+2 by omega, show k+9-8=k+1 by omega]
  have h := congrArg (fun n : ℤ => (n : ℚ)) (numerator_residual k)
  push_cast at h
  unfold a
  linear_combination h / 4

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
theorem generating_function :
    (1 - C 8 * X ^ 1 + C 16 * X ^ 2 + C 20 * X ^ 3 - C 95 * X ^ 4 +
      C 60 * X ^ 5 + C 80 * X ^ 6 - C 100 * X ^ 7 + C 25 * X ^ 8 : ℚ⟦X⟧) * mk series =
      X ^ 1 - C 6 * X ^ 2 + C 4 * X ^ 3 + C 30 * X ^ 4 - C 45 * X ^ 5 -
        C 22 * X ^ 6 + C 60 * X ^ 7 - C 20 * X ^ 8 := by
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n < 9
  · interval_cases n <;> decide +kernel
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega), if_pos (show 8 ≤ n by omega),
      if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega), if_neg (show n ≠ 8 by omega),
      series, if_neg (show n ≠ 0 by omega), if_neg (show n - 1 ≠ 0 by omega),
      if_neg (show n - 2 ≠ 0 by omega), if_neg (show n - 3 ≠ 0 by omega),
      if_neg (show n - 4 ≠ 0 by omega), if_neg (show n - 5 ≠ 0 by omega),
      if_neg (show n - 6 ≠ 0 by omega), if_neg (show n - 7 ≠ 0 by omega),
      if_neg (show n - 8 ≠ 0 by omega)]
    have h := recurrence n (by omega)
    linarith

end OpenMath.A303930

theorem OMA.solution : type_of% @OMA.S_oeis_a303930.main :=
  ⟨OpenMath.A303930.recurrence, OpenMath.A303930.generating_function⟩
