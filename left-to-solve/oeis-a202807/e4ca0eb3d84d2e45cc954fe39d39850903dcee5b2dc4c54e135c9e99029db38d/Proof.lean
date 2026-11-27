import OMAStatements.S_oeis_a202807
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace A202807Proof

open Finset Matrix PowerSeries
open scoped PowerSeries

open OMA.S_oeis_a202807

private def weight (row : Row) : ℕ := firstHeight row + secondHeight row

private def strict : Matrix Row Row ℤ := fun old new =>
  if follows old new ∧ old ≠ new then 1 else 0

private theorem transition_eq : transition = strict + 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [transition, strict, follows]
  · simp [transition, strict, h]

private theorem weight_bound (row : Row) : weight row ≤ 6 := by
  fin_cases row <;> decide

private theorem strict_increases {i j : Row} (h : strict i j ≠ 0) : weight i < weight j := by
  have hf : follows i j ∧ i ≠ j := by
    by_contra hc
    apply h
    simp [strict, hc]
  rcases hf with ⟨⟨h₁, _, h₂, _⟩, hne⟩
  by_contra hc
  apply hne
  apply Fin.ext
  simp only [weight, firstHeight, secondHeight] at *
  omega

private theorem power_support (k : ℕ) (i j : Row) (h : weight j < weight i + k) :
    (strict ^ k) i j = 0 := by
  induction k generalizing i with
  | zero =>
    have hn : i ≠ j := by rintro rfl; omega
    simp [hn]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : strict i s = 0
    · simp [hs]
    · rw [ih s (by have := strict_increases hs; omega), mul_zero]

private def strictCount (k : ℕ) : ℤ := ∑ row : Row, (strict ^ k) 0 row

private theorem strictCount_zero (k : ℕ) (h : 7 ≤ k) : strictCount k = 0 := by
  apply Finset.sum_eq_zero
  intro r _
  exact power_support k 0 r (by have := weight_bound r; omega)

private theorem expansion (n : ℕ) :
    a (n+1) = ∑ j ∈ range 7, (n.choose j : ℤ) * strictCount j := by
  have hc := (Commute.one_right strict).add_pow' n
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => n.choose i • (strict ^ i * (1 : Matrix Row Row ℤ) ^ j))] at hc
  simp only [one_pow, mul_one] at hc
  change (∑ row : Row, (transition ^ n) 0 row) = _
  rw [transition_eq, hc]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  simp only [nsmul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  change (∑ j ∈ range (n+1), (n.choose j : ℤ) * strictCount j) = _
  by_cases hn : n + 1 ≤ 7
  · apply Finset.sum_subset (range_mono hn)
    intro j _ hj
    have hj' : n < j := by simp only [mem_range] at hj; omega
    rw [Nat.choose_eq_zero_of_lt hj', Nat.cast_zero]
    simp
  · symm
    apply Finset.sum_subset (range_mono (by omega))
    intro j _ hj
    have hj' : 7 ≤ j := by simp only [mem_range] at hj; omega
    rw [strictCount_zero j hj']
    simp

private noncomputable def basis (j : ℕ) : ℤ⟦X⟧ :=
  X^(j+1) * (invOneSubPow ℤ (j+1)).val

private theorem basis_coeff (j n : ℕ) :
    coeff (n+1) (basis j) = (n.choose j : ℤ) := by
  rw [basis, coeff_X_pow_mul', invOneSubPow_val_succ_eq_mk_add_choose]
  split_ifs with h
  · rw [coeff_mk, show j + (n + 1 - (j + 1)) = n by omega]
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

private theorem series_expansion :
    mk a = ∑ j ∈ range 7, C (strictCount j) * basis j := by
  ext n
  rw [map_sum, coeff_mk]
  simp only [coeff_C_mul]
  cases n with
  | zero => simp [a, basis, coeff_X_pow_mul']
  | succ n => simpa only [basis_coeff, mul_comm] using expansion n

private theorem basis_denominator {j : ℕ} (hj : j < 7) :
    ((1-X)^7 : ℤ⟦X⟧) * basis j = X^(j+1) * (1-X)^(6-j) := by
  unfold basis
  calc
    _ = X^(j+1) * (((1-X)^7 : ℤ⟦X⟧) * (invOneSubPow ℤ (j+1)).val) := by ring
    _ = _ := by
      have hp : ((1-X)^7 : ℤ⟦X⟧) = (1-X)^((6-j)+(j+1)) := by
        congr 1
        omega
      rw [hp, one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow]

private def paths : ℕ → Row → ℤ
  | 0, _ => 1
  | n + 1, r => ∑ s : Row, if follows r s ∧ r ≠ s then paths n s else 0

private theorem paths_eq (n : ℕ) (r : Row) : paths n r = ∑ s : Row, (strict ^ n) r s := by
  induction n generalizing r with
  | zero => simp [paths, Matrix.one_apply]
  | succ n ih =>
    simp only [paths, ih, pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : follows r s ∧ r ≠ s <;> simp [strict, h]

private theorem strictCount_eq (n : ℕ) : strictCount n = paths n 0 := (paths_eq n 0).symm

private theorem c0 : strictCount 0 = 1 := by rw [strictCount_eq]; decide
private theorem c1 : strictCount 1 = 5 := by rw [strictCount_eq]; decide
private theorem c2 : strictCount 2 = 21 := by rw [strictCount_eq]; decide
private theorem c3 : strictCount 3 = 42 := by rw [strictCount_eq]; decide
private theorem c4 : strictCount 4 = 41 := by rw [strictCount_eq]; decide
private theorem c5 : strictCount 5 = 20 := by rw [strictCount_eq]; decide
private theorem c6 : strictCount 6 = 4 := by rw [strictCount_eq]; decide

theorem generating_function :
    ((1-X)^7 : ℤ⟦X⟧) * mk a = X*(1-X+11*X^2-12*X^3+6*X^4-X^5) := by
  rw [series_expansion, Finset.mul_sum]
  have h : (∑ j ∈ range 7, ((1-X)^7 : ℤ⟦X⟧) * (C (strictCount j) * basis j)) =
      ∑ j ∈ range 7, C (strictCount j) * (X^(j+1) * (1-X)^(6-j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_left_comm, basis_denominator (mem_range.mp hj)]
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5, c6]
  norm_num [map_ofNat]
  ring

theorem recurrence (n : ℕ) (hn : 7 < n) :
    a n = 7*a (n-1)-21*a (n-2)+35*a (n-3)-35*a (n-4)+21*a (n-5)-7*a (n-6)+a (n-7) := by
  let F := mk a
  have leftExpansion : ((1-X)^7 : ℤ⟦X⟧) * F = F - C 7*(X^1*F) + C 21*(X^2*F) -
      C 35*(X^3*F) + C 35*(X^4*F) - C 21*(X^5*F) + C 7*(X^6*F) - X^7*F := by
    simp only [map_ofNat]
    ring
  have rightExpansion : (X*(1-X+11*X^2-12*X^3+6*X^4-X^5) : ℤ⟦X⟧) =
      X^1 - X^2 + C 11*X^3 - C 12*X^4 + C 6*X^5 - X^6 := by
    simp only [map_ofNat]
    ring
  have h := generating_function
  change ((1-X)^7 : ℤ⟦X⟧) * F = _ at h
  rw [leftExpansion, rightExpansion] at h
  have he := congrArg (coeff n) h
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', F, coeff_mk,
    coeff_X_pow, show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
    show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
    show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
    show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, if_true, if_false] at he
  omega

theorem main :
    (((1-X)^7 : ℤ⟦X⟧) * mk a = X*(1-X+11*X^2-12*X^3+6*X^4-X^5)) ∧
    (∀ n : ℕ, 7 < n →
      a n = 7*a (n-1)-21*a (n-2)+35*a (n-3)-35*a (n-4)+21*a (n-5)-7*a (n-6)+a (n-7)) := ⟨generating_function, recurrence⟩

end A202807Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a202807.main := A202807Proof.main
