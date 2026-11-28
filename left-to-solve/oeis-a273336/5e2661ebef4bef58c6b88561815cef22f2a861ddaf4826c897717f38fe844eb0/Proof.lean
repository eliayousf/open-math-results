import OMAStatements.S_oeis_a273336

/-!
Robert Price introduced the sequence, and Colin Barker conjectured the formulas.
Source: https://oeis.org/A273336
-/

namespace A273336Proof

open OMA.S_oeis_a273336 PowerSeries

private def hole (x y : ℤ) : Bool := decide (¬ (x = 0 ∧ y = 0))

private def outside (n : ℕ) (x y : ℤ) : Prop :=
  (n : ℤ) < x ∨ x < -(n : ℤ) ∨ (n : ℤ) < y ∨ y < -(n : ℤ)

private theorem background (n : ℕ) (x y : ℤ) (h : outside n x y) :
    state n x y = decide (0 < n) := by
  induction n generalizing x y with
  | zero =>
      have hp : ¬ (x = 0 ∧ y = 0) := by
        simp only [outside, Nat.cast_zero, neg_zero] at h
        omega
      simp [state, hp]
  | succ n ih =>
      have hc : outside n x y := by unfold outside at *; omega
      have h₁ : outside n (x - 1) y := by unfold outside at *; omega
      have h₂ : outside n (x + 1) y := by unfold outside at *; omega
      have h₃ : outside n x (y - 1) := by unfold outside at *; omega
      have h₄ : outside n x (y + 1) := by unfold outside at *; omega
      simp only [state, ih _ _ hc, ih _ _ h₁, ih _ _ h₂, ih _ _ h₃, ih _ _ h₄]
      have hnext : 0 < n + 1 := Nat.zero_lt_succ n
      by_cases hn : 0 < n
      · simpa [hn, hnext] using (show (657 : ℕ).testBit 9 = true by decide)
      · simp [hn, hnext]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem third_grid : ∀ i j : Fin 7,
    state 3 ((i.val : ℤ) - 3) ((j.val : ℤ) - 3) = hole ((i.val : ℤ) - 3) ((j.val : ℤ) - 3) := by
  decide

private theorem third_stage (x y : ℤ) : state 3 x y = hole x y := by
  by_cases h : outside 3 x y
  · have hp : ¬ (x = 0 ∧ y = 0) := by
      unfold outside at h
      omega
    simp [background _ _ _ h, hole, hp]
  · unfold outside at h
    let i : Fin 7 := ⟨(x + 3).toNat, by omega⟩
    let j : Fin 7 := ⟨(y + 3).toNat, by omega⟩
    have hi : (i.val : ℤ) - 3 = x := by dsimp [i]; omega
    have hj : (j.val : ℤ) - 3 = y := by dsimp [j]; omega
    simpa only [hi, hj] using third_grid i j

private theorem fixed_step {n : ℕ} (h : ∀ x y, state n x y = hole x y) (x y : ℤ) :
    state (n + 1) x y = hole x y := by
  simp only [state, h]
  by_cases hp : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := hp
    decide
  by_cases h₁ : x - 1 = 0 ∧ y = 0
  · obtain ⟨hx, rfl⟩ := h₁
    have hx' : x = 1 := by omega
    subst x
    decide
  by_cases h₂ : x + 1 = 0 ∧ y = 0
  · obtain ⟨hx, rfl⟩ := h₂
    have hx' : x = -1 := by omega
    subst x
    decide
  by_cases h₃ : x = 0 ∧ y - 1 = 0
  · obtain ⟨rfl, hy⟩ := h₃
    have hy' : y = 1 := by omega
    subst y
    decide
  by_cases h₄ : x = 0 ∧ y + 1 = 0
  · obtain ⟨rfl, hy⟩ := h₄
    have hy' : y = -1 := by omega
    subst y
    decide
  simp only [hole, hp, h₁, h₂, h₃, h₄]
  decide

private theorem stable (k : ℕ) : ∀ x y, state (3 + k) x y = hole x y := by
  induction k with
  | zero => exact third_stage
  | succ k ih => exact fixed_step ih

private theorem permanent (t : ℕ) (ht : 2 < t) (x y : ℤ) : state t x y = hole x y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ t by omega)
  exact stable k x y

private theorem count_formula (t : ℕ) (ht : 2 < t) : count t = 4 * t * (t + 1) := by
  let side := Finset.Icc (-(t : ℤ)) t
  let box := side ×ˢ side
  have hz : (0, 0) ∈ box := by
    simp [box, side, Finset.mem_product]
  have heq : (box.filter (fun p => state t p.1 p.2 = true)) = box.erase (0, 0) := by
    ext p
    obtain ⟨x, y⟩ := p
    simp [Finset.mem_filter, Finset.mem_erase, permanent t ht, hole, Prod.mk.injEq, and_comm]
    tauto
  have hside : side.card = 2 * t + 1 := by
    unfold side
    rw [Int.card_Icc]
    omega
  change (box.filter (fun p => state t p.1 p.2 = true)).card = _
  rw [heq, Finset.card_erase_of_mem hz]
  simp only [box, Finset.card_product, hside]
  rw [show (2 * t + 1) * (2 * t + 1) = 4 * t * (t + 1) + 1 by ring]
  simp

private theorem sum_step (n : ℕ) : a (n + 1) = a n + count (n + 1) :=
  Finset.sum_range_succ count (n + 1)

private theorem closed (n : ℕ) (hn : 1 < n) :
    (a n : ℚ) = 2 / 3 * (2 * n ^ 3 + 6 * n ^ 2 + 4 * n - 15) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
  clear hn
  induction k with
  | zero =>
      have h : a 2 = 22 := by decide
      norm_num [h]
  | succ k ih =>
      rw [show 2 + (k + 1) = (2 + k) + 1 by omega, sum_step, count_formula _ (by omega)]
      push_cast
      rw [ih]
      push_cast
      ring

private theorem recurrence_rat (n : ℕ) (hn : 5 < n) :
    (a n : ℚ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  rw [closed n (by omega), closed (n - 1) (by omega), closed (n - 2) (by omega),
    closed (n - 3) (by omega), closed (n - 4) (by omega)]
  rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega)]
  ring

private theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  exact_mod_cast recurrence_rat n hn

private theorem generating_function :
    mk (fun n => (a n : ℤ)) * (1 - X) ^ 4 =
      1 + X + 8 * X ^ 2 + 8 * X ^ 3 - 17 * X ^ 4 + 7 * X ^ 5 := by
  let A : ℤ⟦X⟧ := mk (fun n => (a n : ℤ))
  change A * (1 - X) ^ 4 = _
  have hC (k : ℕ) : C (k : ℤ) = (k : ℤ⟦X⟧) := map_natCast C k
  have hc₄ : C (4 : ℤ) = (4 : ℤ⟦X⟧) := hC 4
  have hc₆ : C (6 : ℤ) = (6 : ℤ⟦X⟧) := hC 6
  have hc₇ : C (7 : ℤ) = (7 : ℤ⟦X⟧) := hC 7
  have hc₈ : C (8 : ℤ) = (8 : ℤ⟦X⟧) := hC 8
  have hc₁₇ : C (17 : ℤ) = (17 : ℤ⟦X⟧) := hC 17
  have hleft : A * (1 - X) ^ 4 =
      A - C 4 * (X ^ 1 * A) + C 6 * (X ^ 2 * A) - C 4 * (X ^ 3 * A) + X ^ 4 * A := by
    rw [hc₄, hc₆]
    ring
  rw [hleft, ← hc₈, ← hc₁₇, ← hc₇]
  ext n
  by_cases hn : 5 < n
  · have h₁ : 1 ≤ n := by omega
    have h₂ : 2 ≤ n := by omega
    have h₃ : 3 ≤ n := by omega
    have h₄ : 4 ≤ n := by omega
    have hn₀ : n ≠ 0 := by omega
    have hn₁ : n ≠ 1 := by omega
    have hn₂ : n ≠ 2 := by omega
    have hn₃ : n ≠ 3 := by omega
    have hn₄ : n ≠ 4 := by omega
    have hn₅ : n ≠ 5 := by omega
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', if_pos h₁, if_pos h₂, if_pos h₃,
      if_pos h₄, coeff_X, coeff_one, coeff_X_pow, if_neg hn₀, if_neg hn₁, if_neg hn₂, if_neg hn₃,
      if_neg hn₄, if_neg hn₅, mul_zero, add_zero, sub_zero, A, coeff_mk]
    linarith [recurrence n hn]
  · have a₀ : a 0 = 1 := by decide
    have a₁ : a 1 = 5 := by decide
    have a₂ : a 2 = 22 := by decide
    have a₃ : a 3 = 70 := calc
      a 3 = a 2 + count 3 := by simpa only [Nat.reduceAdd] using sum_step 2
      _ = 70 := by rw [a₂, count_formula 3 (by decide)]
    have a₄ : a 4 = 150 := calc
      a 4 = a 3 + count 4 := by simpa only [Nat.reduceAdd] using sum_step 3
      _ = 150 := by rw [a₃, count_formula 4 (by decide)]
    have a₅ : a 5 = 270 := calc
      a 5 = a 4 + count 5 := by simpa only [Nat.reduceAdd] using sum_step 4
      _ = 270 := by rw [a₄, count_formula 5 (by decide)]
    interval_cases n <;>
      simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X, coeff_X_pow,
        coeff_one, A, coeff_mk] <;>
      norm_num [a₀, a₁, a₂, a₃, a₄, a₅]

end A273336Proof

open A273336Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a273336.main :=
  ⟨closed, recurrence, generating_function⟩
