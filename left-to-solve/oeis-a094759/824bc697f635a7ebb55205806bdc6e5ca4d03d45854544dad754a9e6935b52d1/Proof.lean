import OMAStatements.S_oeis_a094759

open OMA.S_oeis_a094759 ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a094759.main := by
  let f : ℕ → ℕ := fun j => 28 * 5 ^ j
  have hf : StrictMono f := by
    intro i j hij
    exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by decide : (1 : ℕ) < 5) hij) (by decide)
  apply (Set.infinite_range_of_injective hf.injective).mono
  rintro _ ⟨j, rfl⟩
  change 1 ≤ 28 * 5 ^ j ∧ a (28 * 5 ^ j) < 28 * 5 ^ j
  have hp : 0 < 5 ^ j := by positivity
  have hlt : 6 * 5 ^ j < 28 * 5 ^ j := Nat.mul_lt_mul_of_pos_right (by decide) hp
  have h6 : Nat.Coprime 6 (5 ^ j) := (by decide : Nat.Coprime 6 5).pow_right j
  have h28 : Nat.Coprime 28 (5 ^ j) := (by decide : Nat.Coprime 28 5).pow_right j
  have hs6 : sigma 1 6 = 12 := (sigma_one_apply 6).trans (by decide)
  have hs28 : sigma 1 28 = 56 := (sigma_one_apply 28).trans (by decide)
  have heq : 28 * 5 ^ j * sigma 1 (6 * 5 ^ j) =
      6 * 5 ^ j * sigma 1 (28 * 5 ^ j) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime h6, isMultiplicative_sigma.map_mul_of_coprime h28,
      hs6, hs28]
    ring
  have hmem : 6 * 5 ^ j ∈ {k : ℕ | 1 ≤ k ∧ k ≤ 28 * 5 ^ j ∧
      28 * 5 ^ j * sigma 1 k = k * sigma 1 (28 * 5 ^ j)} :=
    ⟨by omega, hlt.le, heq⟩
  exact ⟨by omega, lt_of_le_of_lt (Nat.sInf_le hmem) hlt⟩
