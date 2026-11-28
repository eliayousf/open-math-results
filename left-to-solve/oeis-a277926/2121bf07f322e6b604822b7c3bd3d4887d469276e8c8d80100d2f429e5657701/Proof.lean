import OMAStatements.S_oeis_a277926

/-!
Robert Price introduced A277926, and Colin Barker conjectured the formulas.
Source: https://oeis.org/A277926
-/

namespace A277926Proof

open OMA.S_oeis_a277926 PowerSeries

private theorem state_one (p : ℤ × ℤ) : state 1 p = decide (p ≠ (0, 0)) := by
  obtain ⟨x, y⟩ := p
  by_cases h : (x, y) = ((0, 0) : ℤ × ℤ)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    decide
  by_cases h₁ : (x + 1, y) = ((0, 0) : ℤ × ℤ) <;>
    by_cases h₂ : (x - 1, y) = ((0, 0) : ℤ × ℤ) <;>
    by_cases h₃ : (x, y + 1) = ((0, 0) : ℤ × ℤ) <;>
    by_cases h₄ : (x, y - 1) = ((0, 0) : ℤ × ℤ) <;>
    simp [state, nbrs, h, h₁, h₂, h₃, h₄, rule] <;>
    simp_all only [Prod.mk.injEq] <;> first | decide | omega

private theorem rule_on (k : ℕ) : rule true k = false := by
  cases k with
  | zero => decide
  | succ k =>
      change (5 : ℕ).testBit (2 * (k + 1) + 1) = false
      apply Nat.testBit_eq_false_of_lt
      have h : 3 ≤ 2 * (k + 1) + 1 := by omega
      exact (show 5 < 2 ^ 3 by decide).trans_le (Nat.pow_le_pow_right (by decide) h)

private theorem state_two (p : ℤ × ℤ) : state 2 p = false := by
  by_cases hp : p = (0, 0)
  · subst p
    decide
  · rw [state, state_one]
    simp [hp, rule_on]

private theorem constant_step {n : ℕ} {b : Bool} (h : ∀ p, state n p = b)
    (p : ℤ × ℤ) : state (n + 1) p = !b := by
  rw [state]
  simp only [nbrs, List.countP_cons, List.countP_nil, h]
  cases b <;> decide

private theorem two_phases (k : ℕ) :
    (∀ p, state (2 * k + 2) p = false) ∧ (∀ p, state (2 * k + 3) p = true) := by
  induction k with
  | zero => exact ⟨state_two, constant_step state_two⟩
  | succ k ih =>
      have h : ∀ p, state (2 * (k + 1) + 2) p = false := by
        rw [show 2 * (k + 1) + 2 = (2 * k + 3) + 1 by omega]
        exact constant_step ih.2
      exact ⟨h, constant_step h⟩

private theorem even_value (n : ℕ) (hn : 1 < n) (he : Even n) : (a n : ℚ) = 0 := by
  obtain ⟨k, hk⟩ := he
  have h : ∀ p, state n p = false := by
    rw [show n = 2 * (k - 1) + 2 by omega]
    exact (two_phases (k - 1)).1
  simp [a, h]

private theorem odd_value (n : ℕ) (hn : 1 < n) (ho : Odd n) :
    (a n : ℚ) = (10 ^ (n + 1) - 1) / 9 := by
  obtain ⟨k, hk⟩ := ho
  have h : ∀ p, state n p = true := by
    rw [show n = 2 * (k - 1) + 3 by omega]
    exact (two_phases (k - 1)).2
  unfold a
  simp only [h, if_true, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
  have hr : (∑ k ∈ Finset.range (n + 1), (10 : ℚ) ^ (n - k)) =
      ∑ k ∈ Finset.range (n + 1), (10 : ℚ) ^ k := by
    simpa only [Nat.add_sub_cancel] using
      Finset.sum_range_reflect (fun k => (10 : ℚ) ^ k) (n + 1)
  rw [hr]
  have hs := geom_sum_mul (10 : ℚ) (n + 1)
  norm_num at hs
  linarith

private theorem recurrence_rat (n : ℕ) (hn : 5 < n) :
    (a n : ℚ) = 101 * a (n - 2) - 100 * a (n - 4) := by
  rcases Nat.even_or_odd n with he | ho
  · have h₂ : Even (n - 2) := by
      obtain ⟨k, hk⟩ := he
      exact ⟨k - 1, by omega⟩
    have h₄ : Even (n - 4) := by
      obtain ⟨k, hk⟩ := he
      exact ⟨k - 2, by omega⟩
    rw [even_value _ (by omega) he, even_value _ (by omega) h₂, even_value _ (by omega) h₄]
    norm_num
  · have h₂ : Odd (n - 2) := by
      obtain ⟨k, hk⟩ := ho
      exact ⟨k - 1, by omega⟩
    have h₄ : Odd (n - 4) := by
      obtain ⟨k, hk⟩ := ho
      exact ⟨k - 2, by omega⟩
    rw [odd_value _ (by omega) ho, odd_value _ (by omega) h₂, odd_value _ (by omega) h₄]
    rw [show n + 1 = (n - 4 + 1) + 4 by omega,
      show n - 2 + 1 = (n - 4 + 1) + 2 by omega, pow_add, pow_add]
    ring

private theorem generating_function :
    A = (1 + 10 * X - 101 * X ^ 2 + 101 * X ^ 3 + 100 * X ^ 4 - 100 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X))⁻¹ := by
  let D : ℚ⟦X⟧ := (1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)
  let N : ℚ⟦X⟧ := 1 + 10 * X - 101 * X ^ 2 + 101 * X ^ 3 + 100 * X ^ 4 - 100 * X ^ 5
  change A = N * D⁻¹
  suffices h : A * D = N by
    rw [← h, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp [D]), mul_one]
  have hC (k : ℕ) : C (k : ℚ) = (k : ℚ⟦X⟧) := map_natCast C k
  have h₁₀ : C (10 : ℚ) = (10 : ℚ⟦X⟧) := hC 10
  have h₁₀₀ : C (100 : ℚ) = (100 : ℚ⟦X⟧) := hC 100
  have h₁₀₁ : C (101 : ℚ) = (101 : ℚ⟦X⟧) := hC 101
  have hleft : A * D = A - C 101 * (X ^ 2 * A) + C 100 * (X ^ 4 * A) := by
    rw [h₁₀₀, h₁₀₁]
    dsimp [D]
    ring
  have hright : N = 1 + C 10 * X - C 101 * X ^ 2 + C 101 * X ^ 3 + C 100 * X ^ 4 -
      C 100 * X ^ 5 := by
    rw [h₁₀, h₁₀₀, h₁₀₁]
  rw [hleft, hright]
  ext n
  by_cases hn : 5 < n
  · have h₂ : 2 ≤ n := by omega
    have h₄ : 4 ≤ n := by omega
    have hn₀ : n ≠ 0 := by omega
    have hn₁ : n ≠ 1 := by omega
    have hn₂ : n ≠ 2 := by omega
    have hn₃ : n ≠ 3 := by omega
    have hn₄ : n ≠ 4 := by omega
    have hn₅ : n ≠ 5 := by omega
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', if_pos h₂, if_pos h₄,
      coeff_X, coeff_one, coeff_X_pow, if_neg hn₀, if_neg hn₁, if_neg hn₂, if_neg hn₃,
      if_neg hn₄, if_neg hn₅, mul_zero, add_zero, sub_zero, A, coeff_mk]
    linarith [recurrence_rat n hn]
  · have a₀ : a 0 = 1 := by decide
    have a₁ : a 1 = 10 := by decide
    have a₂ := even_value 2 (by decide) (by decide)
    have a₃ := odd_value 3 (by decide) (by decide)
    have a₄ := even_value 4 (by decide) (by decide)
    have a₅ := odd_value 5 (by decide) (by decide)
    interval_cases n <;> norm_num [coeff_C_mul, coeff_X_pow_mul', coeff_X, coeff_X_pow,
      coeff_one, A, a₀, a₁, a₂, a₃, a₄, a₅]

end A277926Proof

open OMA.S_oeis_a277926 A277926Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a277926.main := by
  refine ⟨even_value, odd_value, ?_, generating_function⟩
  intro n hn
  exact_mod_cast recurrence_rat n hn
