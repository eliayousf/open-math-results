import OMAStatements.S_oeis_a202808
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace A202808Proof

open Finset Matrix PowerSeries OMA.S_oeis_a202808
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

private theorem row_encoding (r : Row) :
    r.val = 9 * firstHeight r + 3 * (secondHeight r - firstHeight r) +
      (thirdHeight r - secondHeight r) := by
  fin_cases r <;> decide

/-- Each possible literal row `(0, x, y, z)` has one base-three encoding. -/
theorem source_row (x y z : ℕ) (hx : x ≤ 2) (hxy : x ≤ y) (hy : y ≤ x + 2)
    (hyz : y ≤ z) (hz : z ≤ y + 2) :
    ∃! r : Row, firstHeight r = x ∧ secondHeight r = y ∧ thirdHeight r = z := by
  let u := y - x
  let v := z - y
  have hu : u ≤ 2 := by omega
  have hv : v ≤ 2 := by omega
  let r : Row := ⟨9 * x + 3 * u + v, by omega⟩
  have hFirst : firstHeight r = x := by
    change (9*x + 3*u + v) / 9 = x
    omega
  have hDiv : (9*x + 3*u + v) / 3 = 3*x + u := by omega
  have hMod : (3*x + u) % 3 = u := by omega
  have hSecond : secondHeight r = y := by
    change firstHeight r + ((9*x + 3*u + v) / 3) % 3 = y
    rw [hFirst, hDiv, hMod]
    omega
  have hLastDigit : (9*x + 3*u + v) % 3 = v := by omega
  have hThird : thirdHeight r = z := by
    change secondHeight r + (9*x + 3*u + v) % 3 = z
    rw [hSecond, hLastDigit]
    omega
  refine ⟨r, ⟨hFirst, hSecond, hThird⟩, ?_⟩
  intro s hs
  apply Fin.ext
  rw [row_encoding s, hs.1, hs.2.1, hs.2.2]

private def weight (row : Row) : ℕ := firstHeight row + secondHeight row + thirdHeight row

private def strict : Matrix Row Row ℤ := fun old new =>
  if follows old new ∧ old ≠ new then 1 else 0

private theorem transition_eq : transition = strict + 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [transition, strict, follows]
  · simp [transition, strict, h]

private theorem weight_bound (row : Row) : weight row ≤ 12 := by
  fin_cases row <;> decide

private theorem strict_increases {i j : Row} (h : strict i j ≠ 0) : weight i < weight j := by
  have hf : follows i j ∧ i ≠ j := by
    by_contra hc
    apply h
    simp [strict, hc]
  rcases hf with ⟨⟨h₁, _, h₂, _, h₃, _⟩, hne⟩
  by_contra hc
  have he : firstHeight i = firstHeight j ∧ secondHeight i = secondHeight j ∧
      thirdHeight i = thirdHeight j := by
    simp only [weight] at hc
    omega
  apply hne
  apply Fin.ext
  calc
    i.val = 9 * firstHeight i + 3 * (secondHeight i - firstHeight i) +
        (thirdHeight i - secondHeight i) := row_encoding i
    _ = j.val := by rw [he.1, he.2.1, he.2.2, ← row_encoding j]

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

private theorem strictCount_zero (k : ℕ) (h : 13 ≤ k) : strictCount k = 0 := by
  apply Finset.sum_eq_zero
  intro r _
  exact power_support k 0 r (by have := weight_bound r; omega)

private theorem expansion (n : ℕ) :
    a (n+1) = ∑ j ∈ range 13, (n.choose j : ℤ) * strictCount j := by
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
  by_cases hn : n + 1 ≤ 13
  · apply Finset.sum_subset (range_mono hn)
    intro j _ hj
    have hj' : n < j := by simp only [mem_range] at hj; omega
    rw [Nat.choose_eq_zero_of_lt hj', Nat.cast_zero]
    simp
  · symm
    apply Finset.sum_subset (range_mono (by omega))
    intro j _ hj
    have hj' : 13 ≤ j := by simp only [mem_range] at hj; omega
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
    mk a = ∑ j ∈ range 13, C (strictCount j) * basis j := by
  ext n
  rw [map_sum, coeff_mk]
  simp only [coeff_C_mul]
  cases n with
  | zero => simp [a, basis, coeff_X_pow_mul']
  | succ n => simpa only [basis_coeff, mul_comm] using expansion n

private theorem basis_denominator {j : ℕ} (hj : j < 13) :
    ((1-X)^13 : ℤ⟦X⟧) * basis j = X^(j+1) * (1-X)^(12-j) := by
  unfold basis
  calc
    _ = X^(j+1) * (((1-X)^13 : ℤ⟦X⟧) * (invOneSubPow ℤ (j+1)).val) := by ring
    _ = _ := by
      have hp : ((1-X)^13 : ℤ⟦X⟧) = (1-X)^((12-j)+(j+1)) := by
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

/-- Completion counts for each starting row, by the number of strict steps. -/
private def table : ℕ → Array ℕ
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 1 => #[9, 13, 13, 13, 16, 13, 13, 13, 9, 8, 11, 10, 10, 11, 8, 7, 6, 3, 5, 6, 5, 4, 4, 2, 2, 1, 0]
  | 2 => #[102, 142, 130, 127, 135, 88, 90, 68, 31, 64, 76, 56, 58, 48, 23, 22, 12, 3, 21, 18, 9, 9, 5, 1, 1, 0, 0]
  | 3 => #[843, 979, 721, 753, 634, 305, 325, 182, 54, 308, 281, 150, 168, 103, 31, 31, 10, 1, 42, 25, 7, 7, 2, 0, 0, 0, 0]
  | 4 => #[4211, 3997, 2307, 2561, 1723, 603, 662, 271, 51, 807, 576, 217, 258, 114, 20, 20, 3, 0, 41, 16, 2, 2, 0, 0, 0, 0, 0]
  | 5 => #[12932, 10156, 4554, 5310, 2856, 716, 798, 228, 25, 1244, 693, 177, 218, 63, 5, 5, 0, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0]
  | 6 => #[25849, 16881, 5803, 7022, 2952, 507, 568, 102, 5, 1180, 492, 77, 97, 14, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0]
  | 7 => #[34999, 18818, 4818, 5993, 1866, 198, 222, 19, 0, 684, 192, 14, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 8 => #[32611, 14024, 2529, 3213, 663, 33, 37, 0, 0, 224, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 9 => #[20722, 6731, 765, 989, 102, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 10 => #[8619, 1888, 102, 134, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 11 => #[2124, 236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 12 => #[236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | _ => #[]

private def entry (n : ℕ) (r : Row) : ℤ := (table n)[r.val]!

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem table_step (n : Fin 12) (r : Row) :
    entry (n.val + 1) r = ∑ s : Row, if follows r s ∧ r ≠ s then entry n.val s else 0 := by
  revert n r
  decide +kernel

private theorem paths_table (n : ℕ) (hn : n ≤ 12) (r : Row) : paths n r = entry n r := by
  induction n generalizing r with
  | zero => fin_cases r <;> decide
  | succ n ih =>
    have hs := table_step ⟨n, by omega⟩ r
    change entry (n + 1) r = ∑ s : Row, if follows r s ∧ r ≠ s then entry n s else 0 at hs
    rw [paths, hs]
    apply sum_congr rfl
    intro s _
    rw [ih (by omega) s]

private theorem count_by_table (n : ℕ) (hn : n ≤ 12) : strictCount n = entry n 0 :=
  (strictCount_eq n).trans (paths_table n hn 0)

private theorem counts :
    strictCount 0 = 1 ∧ strictCount 1 = 9 ∧ strictCount 2 = 102 ∧
    strictCount 3 = 843 ∧ strictCount 4 = 4211 ∧ strictCount 5 = 12932 ∧
    strictCount 6 = 25849 ∧ strictCount 7 = 34999 ∧ strictCount 8 = 32611 ∧
    strictCount 9 = 20722 ∧ strictCount 10 = 8619 ∧ strictCount 11 = 2124 ∧
    strictCount 12 = 236 := by
  rw [count_by_table 0 (by decide), count_by_table 1 (by decide), count_by_table 2 (by decide), count_by_table 3 (by decide), count_by_table 4 (by decide), count_by_table 5 (by decide), count_by_table 6 (by decide), count_by_table 7 (by decide), count_by_table 8 (by decide), count_by_table 9 (by decide), count_by_table 10 (by decide), count_by_table 11 (by decide), count_by_table 12 (by decide)]
  decide

theorem generating_function :
    ((1-X)^13 : ℤ⟦X⟧) * mk a = X * (1 - 3*X + 69*X^2 + 98*X^3 + 224*X^4 - 470*X^5 +
      607*X^6 - 459*X^7 + 228*X^8 - 71*X^9 + 13*X^10 - X^11) := by
  rw [series_expansion, Finset.mul_sum]
  have h : (∑ j ∈ range 13, ((1-X)^13 : ℤ⟦X⟧) * (C (strictCount j) * basis j)) =
      ∑ j ∈ range 13, C (strictCount j) * (X^(j+1) * (1-X)^(12-j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_left_comm, basis_denominator (mem_range.mp hj)]
  rw [h]
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12⟩ := counts
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12]
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

theorem recurrence (n : ℕ) (hn : 13 < n) :
    a n = 13*a (n-1) - 78*a (n-2) + 286*a (n-3) - 715*a (n-4) + 1287*a (n-5)
      - 1716*a (n-6) + 1716*a (n-7) - 1287*a (n-8) + 715*a (n-9)
      - 286*a (n-10) + 78*a (n-11) - 13*a (n-12) + a (n-13) := by
  let F := mk a
  have leftExpansion : ((1-X)^13 : ℤ⟦X⟧) * F = F - C 13*(X^1*F) + C 78*(X^2*F) - C 286*(X^3*F) + C 715*(X^4*F)
      - C 1287*(X^5*F) + C 1716*(X^6*F) - C 1716*(X^7*F) + C 1287*(X^8*F) - C 715*(X^9*F) + C 286*(X^10*F) - C 78*(X^11*F) + C 13*(X^12*F) - (X^13*F) := by
    simp only [map_ofNat]
    ring
  have rightExpansion : (X * (1 - 3*X + 69*X^2 + 98*X^3 + 224*X^4 - 470*X^5 +
      607*X^6 - 459*X^7 + 228*X^8 - 71*X^9 + 13*X^10 - X^11) : ℤ⟦X⟧) =
      X^1 - C 3*X^2 + C 69*X^3 + C 98*X^4 + C 224*X^5
      - C 470*X^6 + C 607*X^7 - C 459*X^8 + C 228*X^9
      - C 71*X^10 + C 13*X^11 - X^12 := by
    simp only [map_ofNat]
    ring
  have h := generating_function
  change ((1-X)^13 : ℤ⟦X⟧) * F = _ at h
  rw [leftExpansion, rightExpansion] at h
  have he := congrArg (coeff n) h
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', F, coeff_mk, coeff_X_pow,
    show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
    show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega,
    show 7 ≤ n by omega, show 8 ≤ n by omega, show 9 ≤ n by omega,
    show 10 ≤ n by omega, show 11 ≤ n by omega, show 12 ≤ n by omega,
    show 13 ≤ n by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
    show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
    show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega,
    show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega,
    show n ≠ 12 by omega,
    if_true, if_false] at he
  omega

theorem main :
    (∀ n : ℕ, 13 < n → a n = 13*a (n-1) - 78*a (n-2) + 286*a (n-3) - 715*a (n-4) + 1287*a (n-5)
      - 1716*a (n-6) + 1716*a (n-7) - 1287*a (n-8) + 715*a (n-9)
      - 286*a (n-10) + 78*a (n-11) - 13*a (n-12) + a (n-13)) ∧
    (((1-X)^13 : ℤ⟦X⟧) * mk a = X * (1 - 3*X + 69*X^2 + 98*X^3 + 224*X^4 - 470*X^5 +
      607*X^6 - 459*X^7 + 228*X^8 - 71*X^9 + 13*X^10 - X^11)) :=
  ⟨recurrence, generating_function⟩

end A202808Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a202808.main := A202808Proof.main
