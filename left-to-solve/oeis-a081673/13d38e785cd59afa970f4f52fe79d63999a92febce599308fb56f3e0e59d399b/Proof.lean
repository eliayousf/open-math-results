import OMAStatements.S_oeis_a081673

namespace OMA.S_oeis_a081673

open Finset

private def term (n j : ℕ) : ℤ := (n.choose (2 * j) : ℤ) * ((2 * j).choose j : ℤ)

private def tri (n : ℕ) : ℤ := ∑ j ∈ range (n / 2 + 1), term n j

private theorem term_zero {n j : ℕ} (h : n < 2 * j) : term n j = 0 := by
  simp [term, Nat.choose_eq_zero_of_lt h]

private theorem tri_eq_sum {n m : ℕ} (h : n < m) : tri n = ∑ j ∈ range m, term n j := by
  apply sum_subset (range_mono (by omega))
  intro j _ hj
  simp only [mem_range, not_lt] at hj
  exact term_zero (by omega)

private theorem a_eq (n : ℕ) : a n = 3 ^ n - 1 + tri n := rfl

private theorem term_up (n j : ℕ) :
    ((n : ℤ) + 1) * term n j = ((n : ℤ) + 1 - 2 * (j : ℤ)) * term (n + 1) j := by
  by_cases h : 2 * j ≤ n + 1
  · have hh : (n.choose (2 * j) : ℤ) * ((n : ℤ) + 1) =
        ((n + 1).choose (2 * j) : ℤ) * ((n + 1 - 2 * j : ℕ) : ℤ) := by
      exact_mod_cast Nat.choose_mul_succ_eq n (2 * j)
    push_cast [Nat.cast_sub h] at hh
    unfold term
    linear_combination ((2 * j).choose j : ℤ) * hh
  · rw [term_zero (by omega : n < 2 * j), term_zero (by omega : n + 1 < 2 * j)]
    simp

private theorem choose_raise (n j : ℕ) :
    ((n : ℤ) + 1) * (n.choose j : ℤ) = ((n + 1).choose (j + 1) : ℤ) * ((j : ℤ) + 1) := by
  exact_mod_cast Nat.add_one_mul_choose_eq n j

private theorem term_slide (n j : ℕ) :
    ((n : ℤ) + 2) * ((n : ℤ) + 1) * term n j =
      ((j : ℤ) + 1) ^ 2 * term (n + 2) (j + 1) := by
  have hrow1 := choose_raise n (2 * j)
  have hrow2 := choose_raise (n + 1) (2 * j + 1)
  have hrow :
      ((n : ℤ) + 2) * ((n : ℤ) + 1) * (n.choose (2 * j) : ℤ) =
        ((2 : ℤ) * j + 2) * ((2 : ℤ) * j + 1) * ((n + 2).choose (2 * j + 2) : ℤ) := by
    push_cast at hrow1 hrow2
    linear_combination ((n : ℤ) + 2) * hrow1 + ((2 : ℤ) * j + 1) * hrow2
  have hmiddle1 := choose_raise (2 * j) j
  rw [Nat.choose_symm_half] at hmiddle1
  have hmiddle2 := choose_raise (2 * j + 1) j
  have hmiddle :
      ((2 : ℤ) * j + 2) * ((2 : ℤ) * j + 1) * ((2 * j).choose j : ℤ) =
        ((j : ℤ) + 1) ^ 2 * ((2 * j + 2).choose (j + 1) : ℤ) := by
    push_cast at hmiddle1 hmiddle2
    linear_combination ((2 : ℤ) * j + 2) * hmiddle1 + ((j : ℤ) + 1) * hmiddle2
  unfold term
  rw [show 2 * (j + 1) = 2 * j + 2 by omega]
  linear_combination ((2 * j).choose j : ℤ) * hrow + ((n + 2).choose (2 * j + 2) : ℤ) * hmiddle

private theorem term_certificate (n j : ℕ) :
    ((n : ℤ) + 2) * (((n : ℤ) + 2) * term (n + 2) j -
      (2 * ((n : ℤ) + 2) - 1) * term (n + 1) j -
      3 * ((n : ℤ) + 1) * term n j) =
    4 * ((j : ℤ) ^ 2 * term (n + 2) j - ((j : ℤ) + 1) ^ 2 * term (n + 2) (j + 1)) := by
  have hup := term_up (n + 1) j
  have hlow := term_up n j
  push_cast at hup
  linear_combination -((n : ℤ) + 2 + 2 * (j : ℤ)) * hup +
    ((n : ℤ) + 2) * hlow - 4 * term_slide n j

private theorem tri_recurrence (n : ℕ) :
    ((n : ℤ) + 2) * tri (n + 2) -
      (2 * ((n : ℤ) + 2) - 1) * tri (n + 1) -
      3 * ((n : ℤ) + 1) * tri n = 0 := by
  let m := n + 3
  let boundary (j : ℕ) : ℤ := (j : ℤ) ^ 2 * term (n + 2) j
  have hzero : boundary 0 = 0 := by simp [boundary]
  have hlast : boundary m = 0 := by
    have hm : n + 2 < 2 * m := by dsimp [m]; omega
    simp [boundary, term_zero hm]
  have htel := (sum_range_succ' boundary m).symm.trans (sum_range_succ boundary m)
  rw [hzero, hlast, add_zero, add_zero] at htel
  have hs :
      ((n : ℤ) + 2) * (((n : ℤ) + 2) * tri (n + 2) -
        (2 * ((n : ℤ) + 2) - 1) * tri (n + 1) - 3 * ((n : ℤ) + 1) * tri n) = 0 := by
    calc
      _ = ∑ j ∈ range m, ((n : ℤ) + 2) * (((n : ℤ) + 2) * term (n + 2) j -
          (2 * ((n : ℤ) + 2) - 1) * term (n + 1) j - 3 * ((n : ℤ) + 1) * term n j) := by
        rw [tri_eq_sum (n := n + 2) (m := m) (by dsimp [m]; omega),
          tri_eq_sum (n := n + 1) (m := m) (by dsimp [m]; omega),
          tri_eq_sum (n := n) (m := m) (by dsimp [m]; omega)]
        simp only [mul_sub, mul_sum, sum_sub_distrib]
      _ = 4 * ((∑ j ∈ range m, boundary j) - ∑ j ∈ range m, boundary (j + 1)) := by
        rw [← sum_sub_distrib, mul_sum]
        apply sum_congr rfl
        intro j _
        simpa only [boundary, Nat.cast_add, Nat.cast_one] using term_certificate n j
      _ = 0 := by rw [htel, sub_self, mul_zero]
  exact (mul_eq_zero.mp hs).resolve_left (by positivity)

end OMA.S_oeis_a081673

open OMA.S_oeis_a081673 in
theorem OMA.solution : type_of% @OMA.S_oeis_a081673.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega, a_eq,
    Nat.cast_add, Nat.cast_ofNat, pow_add]
  have hhigh := tri_recurrence (k + 2)
  have hmid := tri_recurrence (k + 1)
  have hlow := tri_recurrence k
  push_cast at hhigh hmid
  linear_combination (2 * ((k : ℤ) + 4) - 7) * hhigh +
    (26 - 8 * ((k : ℤ) + 4)) * hmid + 3 * (2 * ((k : ℤ) + 4) - 5) * hlow
