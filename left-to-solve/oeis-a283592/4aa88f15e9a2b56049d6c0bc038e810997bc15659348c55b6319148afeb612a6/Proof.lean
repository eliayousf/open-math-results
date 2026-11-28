import OMAStatements.S_oeis_a283592

/-!
Robert Price introduced A283592, and Colin Barker conjectured the formulas.
Source: https://oeis.org/A283592
-/

namespace A283592Proof

open OMA.S_oeis_a283592 PowerSeries

private def hole (p : ℤ × ℤ) : Bool := decide (p ≠ (0, 0))

private def outside (n : ℕ) (x y : ℤ) : Prop :=
  (n : ℤ) < x ∨ x < -(n : ℤ) ∨ (n : ℤ) < y ∨ y < -(n : ℤ)

private theorem background (n : ℕ) (x y : ℤ) (h : outside n x y) :
    state n (x, y) = decide (0 < n) := by
  induction n generalizing x y with
  | zero =>
      have hp : (x, y) ≠ ((0, 0) : ℤ × ℤ) := by
        simp only [outside, Nat.cast_zero, neg_zero] at h
        intro hp
        obtain ⟨hx, hy⟩ := Prod.mk.inj hp
        omega
      simp [state, hp]
  | succ n ih =>
      have hc : outside n x y := by unfold outside at *; omega
      have h₁ : outside n (x + 1) y := by unfold outside at *; omega
      have h₂ : outside n (x - 1) y := by unfold outside at *; omega
      have h₃ : outside n x (y + 1) := by unfold outside at *; omega
      have h₄ : outside n x (y - 1) := by unfold outside at *; omega
      simp only [state, nbrs, List.countP_cons, List.countP_nil, ih _ _ hc, ih _ _ h₁,
        ih _ _ h₂, ih _ _ h₃, ih _ _ h₄]
      have hn' : 0 < n + 1 := Nat.zero_lt_succ n
      by_cases hn : 0 < n
      · simpa [hn, hn'] using (show rule true 4 = true by decide)
      · simpa [hn, hn'] using (show rule false 0 = true by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem third_grid : ∀ i j : Fin 7,
    state 3 ((i.val : ℤ) - 3, (j.val : ℤ) - 3) =
      hole ((i.val : ℤ) - 3, (j.val : ℤ) - 3) := by decide

private theorem third_stage (p : ℤ × ℤ) : state 3 p = hole p := by
  obtain ⟨x, y⟩ := p
  by_cases h : outside 3 x y
  · have hp : (x, y) ≠ ((0, 0) : ℤ × ℤ) := by
      unfold outside at h
      intro hp
      obtain ⟨hx, hy⟩ := Prod.mk.inj hp
      omega
    simp [background _ _ _ h, hole, hp]
  · unfold outside at h
    let i : Fin 7 := ⟨(x + 3).toNat, by omega⟩
    let j : Fin 7 := ⟨(y + 3).toNat, by omega⟩
    have hi : (i.val : ℤ) - 3 = x := by dsimp [i]; omega
    have hj : (j.val : ℤ) - 3 = y := by dsimp [j]; omega
    simpa only [hi, hj] using third_grid i j

private theorem hole_fixed (p : ℤ × ℤ) :
    rule (hole p) ((nbrs p).countP hole) = hole p := by
  obtain ⟨x, y⟩ := p
  by_cases h : (x, y) = ((0, 0) : ℤ × ℤ)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    decide
  by_cases h₁ : (x + 1, y) = ((0, 0) : ℤ × ℤ) <;>
    by_cases h₂ : (x - 1, y) = ((0, 0) : ℤ × ℤ) <;>
    by_cases h₃ : (x, y + 1) = ((0, 0) : ℤ × ℤ) <;>
    by_cases h₄ : (x, y - 1) = ((0, 0) : ℤ × ℤ) <;>
    simp [hole, nbrs, h, h₁, h₂, h₃, h₄, rule] <;>
    simp_all only [Prod.mk.injEq] <;> first | decide | omega

private theorem stable (k : ℕ) : state (3 + k) = hole := by
  induction k with
  | zero => exact funext third_stage
  | succ k ih =>
      funext p
      rw [show 3 + (k + 1) = (3 + k) + 1 by omega, state, ih]
      exact hole_fixed p

private theorem digit_formula (n : ℕ) (hn : 2 < n) : a n = b n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
  have hs : state n = hole := by
    rw [hk]
    exact stable k
  have digit (i : ℕ) : state n ((i : ℤ), 0) = decide (i ≠ 0) := by
    rw [hs]
    simp [hole, Prod.mk.injEq]
  have hsuc (i : ℕ) : state n (((i + 1 : ℕ) : ℤ), 0) = true := by
    exact (digit (i + 1)).trans (by simp)
  have hzero : state n (((0 : ℕ) : ℤ), 0) = false := by simpa using digit 0
  unfold a b
  rw [Finset.sum_range_succ']
  simp only [hsuc, hzero, Bool.false_eq_true, if_false, if_true, add_zero]
  have hreflect : (∑ i ∈ Finset.range n, (2 : ℕ) ^ (n - (i + 1))) =
      ∑ i ∈ Finset.range n, (2 : ℕ) ^ i := by
    calc
      _ = ∑ i ∈ Finset.range n, (2 : ℕ) ^ (n - 1 - i) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        omega
      _ = _ := Finset.sum_range_reflect (fun i => (2 : ℕ) ^ i) n
  rw [hreflect]
  have hgeom := geom_sum_mul_add (1 : ℕ) n
  norm_num at hgeom
  omega

private theorem closed_rat (n : ℕ) (hn : 2 < n) : (a n : ℚ) = 2 ^ n - 1 := by
  have hpow : 1 ≤ (2 : ℕ) ^ n := by
    have h : 0 < (2 : ℕ) ^ n := by positivity
    omega
  rw [digit_formula n hn, b, Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_one]
  norm_num

private theorem recurrence_rat (n : ℕ) (hn : 4 < n) :
    (a n : ℚ) = 3 * a (n - 1) - 2 * a (n - 2) := by
  rw [closed_rat n (by omega), closed_rat (n - 1) (by omega), closed_rat (n - 2) (by omega)]
  have h₁ : (2 : ℚ) ^ (n - 1) = 2 ^ (n - 2) * 2 ^ 1 := by
    rw [← pow_add]
    congr 1
    omega
  have h₂ : (2 : ℚ) ^ n = 2 ^ (n - 2) * 2 ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [h₂, h₁]
  ring

private theorem generating_function :
    A = (1 - 3 * X + 7 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4) * ((1 - X) * (1 - 2 * X))⁻¹ := by
  let D : ℚ⟦X⟧ := (1 - X) * (1 - 2 * X)
  let N : ℚ⟦X⟧ := 1 - 3 * X + 7 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4
  change A = N * D⁻¹
  suffices h : A * D = N by
    rw [← h, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp [D]), mul_one]
  have hC (k : ℕ) : C (k : ℚ) = (k : ℚ⟦X⟧) := map_natCast C k
  have h₂ : C (2 : ℚ) = (2 : ℚ⟦X⟧) := hC 2
  have h₃ : C (3 : ℚ) = (3 : ℚ⟦X⟧) := hC 3
  have h₄ : C (4 : ℚ) = (4 : ℚ⟦X⟧) := hC 4
  have h₇ : C (7 : ℚ) = (7 : ℚ⟦X⟧) := hC 7
  have h₈ : C (8 : ℚ) = (8 : ℚ⟦X⟧) := hC 8
  have hleft : A * D = A - C 3 * (X * A) + C 2 * (X ^ 2 * A) := by
    rw [h₂, h₃]
    dsimp [D]
    ring
  have hright : N = 1 - C 3 * X + C 7 * X ^ 2 - C 8 * X ^ 3 + C 4 * X ^ 4 := by
    rw [h₃, h₄, h₇, h₈]
  rw [hleft, hright]
  ext n
  by_cases hn : 4 < n
  · have h₁ : 1 ≤ n := by omega
    have h₂ : 2 ≤ n := by omega
    have hn₀ : n ≠ 0 := by omega
    have hn₁ : n ≠ 1 := by omega
    have hn₂ : n ≠ 2 := by omega
    have hn₃ : n ≠ 3 := by omega
    have hn₄ : n ≠ 4 := by omega
    have hshift : coeff n (X * A) = coeff (n - 1) A := by
      simpa using (coeff_X_pow_mul' A 1 n).trans (if_pos h₁)
    simp only [map_add, map_sub, coeff_C_mul, hshift, coeff_X_pow_mul', if_pos h₂,
      coeff_X, coeff_one, coeff_X_pow, if_neg hn₀, if_neg hn₁, if_neg hn₂, if_neg hn₃,
      if_neg hn₄, mul_zero, add_zero, sub_zero]
    simp only [A, coeff_mk]
    linarith [recurrence_rat n hn]
  · have a₀ : a 0 = 1 := by decide
    have a₁ : a 1 = 0 := by decide
    have a₂ : a 2 = 5 := by decide
    have a₃ := closed_rat 3 (by decide)
    have a₄ := closed_rat 4 (by decide)
    interval_cases n <;> norm_num [coeff_C_mul, coeff_X_pow_mul', coeff_X, coeff_X_pow,
      coeff_one, coeff_succ_X_mul, A, a₀, a₁, a₂, a₃, a₄]

end A283592Proof

open OMA.S_oeis_a283592 A283592Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a283592.main := by
  refine ⟨generating_function, closed_rat, digit_formula, ?_⟩
  intro n hn
  exact_mod_cast recurrence_rat n hn
