import OMAStatements.S_oeis_a202919
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace A202919Proof

open Finset Matrix PowerSeries OMA.S_oeis_a202919
open scoped PowerSeries

def transition : Matrix Row Row ℤ := fun old new => if follows old new then 1 else 0

private theorem gridFrom_count (n : ℕ) (r : Row) :
    ((gridFrom n r).card : ℤ) = ∑ s : Row, (transition ^ n) r s := by
  induction n generalizing r with
  | zero => simp [gridFrom, Matrix.one_apply]
  | succ n ih =>
    simp only [gridFrom, card_map, card_sigma, Nat.cast_sum, ih, pow_succ', Matrix.mul_apply]
    rw [sum_filter, Finset.sum_comm (s := univ) (t := univ)]
    apply sum_congr rfl
    intro s _
    by_cases h : follows r s <;> simp [transition, h]

theorem source_row (x y : ℕ) (hx : x ≤ 3) (hy : x ≤ y) (hy' : y ≤ x+3) :
    ∃! r : Row, firstHeight r = x ∧ secondHeight r = y := by
  let r : Row := ⟨4*x+(y-x), by omega⟩
  refine ⟨r, ⟨?_, ?_⟩, ?_⟩
  · change (4*x+(y-x))/4 = x
    omega
  · change (4*x+(y-x))/4 + (4*x+(y-x))%4 = y
    omega
  · intro s hs
    apply Fin.ext
    unfold firstHeight secondHeight at hs
    change s.val = 4*x+(y-x)
    omega

private def weight (row : Row) : ℕ := firstHeight row + secondHeight row

private def strict : Matrix Row Row ℤ := fun old new =>
  if follows old new ∧ old ≠ new then 1 else 0

private theorem transition_eq : transition = strict + 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [transition, strict, follows]
  · simp [transition, strict, h]

private theorem weight_bound (row : Row) : weight row ≤ 9 := by
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

private theorem strictCount_zero (k : ℕ) (h : 10 ≤ k) : strictCount k = 0 := by
  apply Finset.sum_eq_zero
  intro r _
  exact power_support k 0 r (by have := weight_bound r; omega)

private theorem expansion (n : ℕ) :
    a (n+1) = ∑ j ∈ range 10, (n.choose j : ℤ) * strictCount j := by
  have hc := (Commute.one_right strict).add_pow' n
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => n.choose i • (strict ^ i * (1 : Matrix Row Row ℤ) ^ j))] at hc
  simp only [one_pow, mul_one] at hc
  rw [a, gridFrom_count, transition_eq, hc]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  simp only [nsmul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  change (∑ j ∈ range (n+1), (n.choose j : ℤ) * strictCount j) = _
  by_cases hn : n + 1 ≤ 10
  · apply Finset.sum_subset (range_mono hn)
    intro j _ hj
    have hj' : n < j := by simp only [mem_range] at hj; omega
    rw [Nat.choose_eq_zero_of_lt hj', Nat.cast_zero]
    simp
  · symm
    apply Finset.sum_subset (range_mono (by omega))
    intro j _ hj
    have hj' : 10 ≤ j := by simp only [mem_range] at hj; omega
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
    mk a = ∑ j ∈ range 10, C (strictCount j) * basis j := by
  ext n
  rw [map_sum, coeff_mk]
  simp only [coeff_C_mul]
  cases n with
  | zero => simp [a, basis, coeff_X_pow_mul']
  | succ n => simpa only [basis_coeff, mul_comm] using expansion n

private theorem basis_denominator {j : ℕ} (hj : j < 10) :
    ((1-X)^10 : ℤ⟦X⟧) * basis j = X^(j+1) * (1-X)^(9-j) := by
  unfold basis
  calc
    _ = X^(j+1) * (((1-X)^10 : ℤ⟦X⟧) * (invOneSubPow ℤ (j+1)).val) := by ring
    _ = _ := by
      have hp : ((1-X)^10 : ℤ⟦X⟧) = (1-X)^((9-j)+(j+1)) := by
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

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem counts :
    strictCount 0 = 1 ∧ strictCount 1 = 9 ∧ strictCount 2 = 71 ∧ strictCount 3 = 293 ∧
    strictCount 4 = 675 ∧ strictCount 5 = 951 ∧ strictCount 6 = 850 ∧ strictCount 7 = 474 ∧
    strictCount 8 = 151 ∧ strictCount 9 = 21 := by
  simp only [strictCount_eq]
  decide +kernel

theorem generating_function :
    ((1-X)^10 : ℤ⟦X⟧) * mk a = X*(1+35*X^2-36*X^3+30*X^4-10*X^5+X^6) := by
  rw [series_expansion, Finset.mul_sum]
  have h : (∑ j ∈ range 10, ((1-X)^10 : ℤ⟦X⟧) * (C (strictCount j) * basis j)) =
      ∑ j ∈ range 10, C (strictCount j) * (X^(j+1) * (1-X)^(9-j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_left_comm, basis_denominator (mem_range.mp hj)]
  rw [h]
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9⟩ := counts
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9]
  norm_num [map_ofNat]
  ring

/-- Successive rows satisfy the vertical increment rule. -/
def validAfter (r : Row) : List Row → Prop
  | [] => True
  | s :: xs => follows r s ∧ validAfter s xs

theorem mem_gridFrom (n : ℕ) (r : Row) (xs : List Row) :
    xs ∈ gridFrom n r ↔ xs.length = n ∧ validAfter r xs := by
  induction n generalizing r xs with
  | zero => cases xs <;> simp [gridFrom, validAfter]
  | succ n ih =>
    cases xs with
    | nil =>
      constructor
      · intro h
        obtain ⟨⟨s,l⟩,_,he⟩ := mem_map.mp h
        change s::l = [] at he
        cases he
      · simp
    | cons s xs =>
      constructor
      · intro h
        obtain ⟨⟨t,l⟩,hm,he⟩ := mem_map.mp h
        change t::l = s::xs at he
        obtain ⟨rfl,rfl⟩ := List.cons.inj he
        have h := mem_sigma.mp hm
        have hl := (ih t l).mp h.2
        exact ⟨by simp [hl.1], (mem_filter.mp h.1).2, hl.2⟩
      · rintro ⟨hlen,hs,hxs⟩
        apply mem_map.mpr
        refine ⟨⟨s,xs⟩, mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _, hs⟩, ?_⟩, rfl⟩
        exact (ih s xs).mpr ⟨by simpa using hlen, hxs⟩

theorem recurrence (n : ℕ) (hn : 10 < n) :
    a n = 10*a (n-1)-45*a (n-2)+120*a (n-3)-210*a (n-4)+252*a (n-5)-
      210*a (n-6)+120*a (n-7)-45*a (n-8)+10*a (n-9)-a (n-10) := by
  let F := mk a
  have leftExpansion : ((1-X)^10 : ℤ⟦X⟧) * F = F - C 10*(X^1*F) + C 45*(X^2*F) -
      C 120*(X^3*F) + C 210*(X^4*F) - C 252*(X^5*F) + C 210*(X^6*F) -
      C 120*(X^7*F) + C 45*(X^8*F) - C 10*(X^9*F) + X^10*F := by
    simp only [map_ofNat]
    ring
  have rightExpansion : (X*(1+35*X^2-36*X^3+30*X^4-10*X^5+X^6) : ℤ⟦X⟧) =
      X^1 + C 35*X^3 - C 36*X^4 + C 30*X^5 - C 10*X^6 + X^7 := by
    simp only [map_ofNat]
    ring
  have h := generating_function
  change ((1-X)^10 : ℤ⟦X⟧) * F = _ at h
  rw [leftExpansion, rightExpansion] at h
  have he := congrArg (coeff n) h
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', F, coeff_mk, coeff_X_pow,
    show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
    show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega,
    show 9 ≤ n by omega, show 10 ≤ n by omega, show n ≠ 1 by omega, show n ≠ 3 by omega,
    show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega,
    if_true, if_false] at he
  omega

theorem main :
    (∀ n : ℕ, 10 < n → a n = 10*a (n-1)-45*a (n-2)+120*a (n-3)-210*a (n-4)+252*a (n-5)-
      210*a (n-6)+120*a (n-7)-45*a (n-8)+10*a (n-9)-a (n-10)) ∧
    (((1-X)^10 : ℤ⟦X⟧) * mk a = X*(1+35*X^2-36*X^3+30*X^4-10*X^5+X^6)) :=
  ⟨recurrence, generating_function⟩

end A202919Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a202919.main := A202919Proof.main
