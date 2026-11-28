import OMAStatements.S_oeis_a277936

/-!
Robert Price introduced A277936, and Colin Barker conjectured the formulas.
Source: https://oeis.org/A277936
-/

namespace A277936Proof

open OMA.S_oeis_a277936 PowerSeries

private theorem state_one (p : ℤ × ℤ) : state 1 p = true := by
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

private theorem constant_step {n : ℕ} {b : Bool} (h : ∀ p, state n p = b)
    (p : ℤ × ℤ) : state (n + 1) p = !b := by
  rw [state]
  simp only [nbrs, List.countP_cons, List.countP_nil, h]
  cases b <;> decide

private theorem two_phases (k : ℕ) :
    (∀ p, state (2 * k + 1) p = true) ∧ (∀ p, state (2 * k + 2) p = false) := by
  induction k with
  | zero => exact ⟨state_one, constant_step state_one⟩
  | succ k ih =>
      have h : ∀ p, state (2 * (k + 1) + 1) p = true := by
        rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega]
        exact constant_step ih.2
      exact ⟨h, constant_step h⟩

private theorem even_value (n : ℕ) (hn : 0 < n) (he : Even n) : (a n : ℚ) = 0 := by
  obtain ⟨k, hk⟩ := he
  have h : ∀ p, state n p = false := by
    rw [show n = 2 * (k - 1) + 2 by omega]
    exact (two_phases (k - 1)).2
  simp [a, h]

private theorem odd_value (n : ℕ) (ho : Odd n) :
    (a n : ℚ) = 2 ^ (n + 1) - 1 := by
  obtain ⟨k, hk⟩ := ho
  have h : ∀ p, state n p = true := by
    rw [hk]
    exact (two_phases k).1
  unfold a
  simp only [h, if_true, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
  have hr : (∑ k ∈ Finset.range (n + 1), (2 : ℚ) ^ (n - k)) =
      ∑ k ∈ Finset.range (n + 1), (2 : ℚ) ^ k := by
    simpa only [Nat.add_sub_cancel] using
      Finset.sum_range_reflect (fun k => (2 : ℚ) ^ k) (n + 1)
  rw [hr]
  have hs := geom_sum_mul (2 : ℚ) (n + 1)
  norm_num at hs
  exact hs

private theorem recurrence_rat (n : ℕ) (hn : 4 < n) :
    (a n : ℚ) = 5 * a (n - 2) - 4 * a (n - 4) := by
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
    rw [odd_value _ ho, odd_value _ h₂, odd_value _ h₄]
    rw [show n + 1 = (n - 4 + 1) + 4 by omega,
      show n - 2 + 1 = (n - 4 + 1) + 2 by omega, pow_add, pow_add]
    ring

private theorem generating_function :
    A = (1 + 3 * X - 5 * X ^ 2 + 4 * X ^ 4) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X))⁻¹ := by
  let D : ℚ⟦X⟧ := (1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)
  let N : ℚ⟦X⟧ := 1 + 3 * X - 5 * X ^ 2 + 4 * X ^ 4
  change A = N * D⁻¹
  suffices h : A * D = N by
    rw [← h, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp [D]), mul_one]
  have hC (k : ℕ) : C (k : ℚ) = (k : ℚ⟦X⟧) := map_natCast C k
  have h₃ : C (3 : ℚ) = (3 : ℚ⟦X⟧) := hC 3
  have h₄ : C (4 : ℚ) = (4 : ℚ⟦X⟧) := hC 4
  have h₅ : C (5 : ℚ) = (5 : ℚ⟦X⟧) := hC 5
  have hleft : A * D = A - C 5 * (X ^ 2 * A) + C 4 * (X ^ 4 * A) := by
    rw [h₄, h₅]
    dsimp [D]
    ring
  have hright : N = 1 + C 3 * X - C 5 * X ^ 2 + C 4 * X ^ 4 := by
    rw [h₃, h₄, h₅]
  rw [hleft, hright]
  ext n
  by_cases hn : 4 < n
  · have h₂ : 2 ≤ n := by omega
    have h₄ : 4 ≤ n := by omega
    have hn₀ : n ≠ 0 := by omega
    have hn₁ : n ≠ 1 := by omega
    have hn₂ : n ≠ 2 := by omega
    have hn₄ : n ≠ 4 := by omega
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', if_pos h₂, if_pos h₄,
      coeff_X, coeff_one, coeff_X_pow, if_neg hn₀, if_neg hn₁, if_neg hn₂,
      if_neg hn₄, mul_zero, add_zero, sub_zero, A, coeff_mk]
    linarith [recurrence_rat n hn]
  · have a₀ : a 0 = 1 := by decide
    have a₁ : a 1 = 3 := by decide
    have a₂ := even_value 2 (by decide) (by decide)
    have a₃ := odd_value 3 (by decide)
    have a₄ := even_value 4 (by decide) (by decide)
    interval_cases n <;> norm_num [coeff_C_mul, coeff_X_pow_mul', coeff_X, coeff_X_pow,
      coeff_one, A, a₀, a₁, a₂, a₃, a₄]

private theorem signed_value (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = -1 / 2 - (-2) ^ n + (-1) ^ n / 2 + 2 ^ n := by
  rw [show (-2 : ℚ) = (-1) * 2 by norm_num, mul_pow]
  rcases Nat.even_or_odd n with he | ho
  · rw [even_value n hn he, he.neg_one_pow]
    ring
  · rw [odd_value n ho, ho.neg_one_pow, pow_succ (2 : ℚ) n]
    ring

end A277936Proof

open OMA.S_oeis_a277936 A277936Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a277936.main := by
  refine ⟨generating_function, ?_, signed_value⟩
  intro n hn
  exact_mod_cast recurrence_rat n hn
