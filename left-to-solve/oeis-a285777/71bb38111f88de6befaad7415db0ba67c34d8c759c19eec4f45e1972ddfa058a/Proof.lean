import OMAStatements.S_oeis_a285777

/-!
Robert Price introduced A285777, and Colin Barker conjectured the formulas.
Source: https://oeis.org/A285777
-/

namespace A285777Proof

open OMA.S_oeis_a285777 PowerSeries

private def outside (n : ℕ) (x y : ℤ) : Prop :=
  (n : ℤ) < x ∨ x < -(n : ℤ) ∨ (n : ℤ) < y ∨ y < -(n : ℤ)

private theorem background (n : ℕ) (x y : ℤ) (h : outside n x y) :
    state n x y = decide (n % 2 = 1) := by
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
      by_cases hn : n % 2 = 1
      · have hnext : (n + 1) % 2 ≠ 1 := by omega
        simpa [hn, hnext] using (show (89 : ℕ).testBit 9 = false by decide)
      · have hnext : (n + 1) % 2 = 1 := by omega
        simp [hn, hnext]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fourth_grid : ∀ i j : Fin 9,
    state 4 ((i.val : ℤ) - 4) ((j.val : ℤ) - 4) = false := by decide

private theorem fourth_stage (x y : ℤ) : state 4 x y = false := by
  by_cases h : outside 4 x y
  · simpa using background 4 x y h
  · unfold outside at h
    let i : Fin 9 := ⟨(x + 4).toNat, by omega⟩
    let j : Fin 9 := ⟨(y + 4).toNat, by omega⟩
    have hi : (i.val : ℤ) - 4 = x := by dsimp [i]; omega
    have hj : (j.val : ℤ) - 4 = y := by dsimp [j]; omega
    simpa only [hi, hj] using fourth_grid i j

private theorem constant_step {n : ℕ} {b : Bool} (h : ∀ x y, state n x y = b)
    (x y : ℤ) : state (n + 1) x y = !b := by
  simp only [state, h]
  cases b <;> decide

private theorem two_phases (k : ℕ) :
    (∀ x y, state (2 * k + 4) x y = false) ∧ (∀ x y, state (2 * k + 5) x y = true) := by
  induction k with
  | zero => exact ⟨fourth_stage, constant_step fourth_stage⟩
  | succ k ih =>
      have h : ∀ x y, state (2 * (k + 1) + 4) x y = false := by
        rw [show 2 * (k + 1) + 4 = (2 * k + 5) + 1 by omega]
        exact constant_step ih.2
      exact ⟨h, constant_step h⟩

private theorem even_value (n : ℕ) (hn : 3 < n) (he : Even n) : a n = 0 := by
  obtain ⟨k, hk⟩ := he
  have h : ∀ x y, state n x y = false := by
    rw [show n = 2 * (k - 2) + 4 by omega]
    exact (two_phases (k - 2)).1
  simp [a, h]

private theorem odd_value (n : ℕ) (hn : 3 < n) (ho : Odd n) :
    (a n : ℤ) = 2 ^ (n + 1) - 1 := by
  obtain ⟨k, hk⟩ := ho
  have h : ∀ x y, state n x y = true := by
    rw [show n = 2 * (k - 2) + 5 by omega]
    exact (two_phases (k - 2)).2
  unfold a
  simp only [h, if_true, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
  simpa using geom_sum_mul (2 : ℤ) (n + 1)

private theorem recurrence (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4) := by
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
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 + 2 * X - 4 * X ^ 2 + 4 * X ^ 3 - X ^ 4 + X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 := by
  let A : ℤ⟦X⟧ := mk (fun n => (a n : ℤ))
  let D : ℤ⟦X⟧ := (1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)
  let N : ℤ⟦X⟧ := 1 + 2 * X - 4 * X ^ 2 + 4 * X ^ 3 - X ^ 4 + X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7
  change A * D = N
  have hC (k : ℕ) : C (k : ℤ) = (k : ℤ⟦X⟧) := map_natCast C k
  have hc₂ : C (2 : ℤ) = (2 : ℤ⟦X⟧) := hC 2
  have hc₄ : C (4 : ℤ) = (4 : ℤ⟦X⟧) := hC 4
  have hc₅ : C (5 : ℤ) = (5 : ℤ⟦X⟧) := hC 5
  have hleft : A * D = A - C 5 * (X ^ 2 * A) + C 4 * (X ^ 4 * A) := by
    rw [hc₄, hc₅]
    dsimp [D]
    ring
  have hright : N = 1 + C 2 * X - C 4 * X ^ 2 + C 4 * X ^ 3 - X ^ 4 + X ^ 5 +
      C 4 * X ^ 6 - C 4 * X ^ 7 := by
    rw [hc₂, hc₄]
  rw [hleft, hright]
  ext n
  by_cases hn : 7 < n
  · have h₂ : 2 ≤ n := by omega
    have h₄ : 4 ≤ n := by omega
    have hn₀ : n ≠ 0 := by omega
    have hn₁ : n ≠ 1 := by omega
    have hn₂ : n ≠ 2 := by omega
    have hn₃ : n ≠ 3 := by omega
    have hn₄ : n ≠ 4 := by omega
    have hn₅ : n ≠ 5 := by omega
    have hn₆ : n ≠ 6 := by omega
    have hn₇ : n ≠ 7 := by omega
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', if_pos h₂, if_pos h₄,
      coeff_X, coeff_one, coeff_X_pow, if_neg hn₀, if_neg hn₁, if_neg hn₂, if_neg hn₃,
      if_neg hn₄, if_neg hn₅, if_neg hn₆, if_neg hn₇, mul_zero, add_zero, sub_zero, A, coeff_mk]
    linarith [recurrence n hn]
  · have a₀ : a 0 = 1 := by decide
    have a₁ : a 1 = 2 := by decide
    have a₂ : a 2 = 1 := by decide
    have a₃ : a 3 = 14 := by decide
    have a₄ := even_value 4 (by decide) (by decide)
    have a₅ := odd_value 5 (by decide) (by decide)
    have a₆ := even_value 6 (by decide) (by decide)
    have a₇ := odd_value 7 (by decide) (by decide)
    interval_cases n <;>
      simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X, coeff_X_pow,
        coeff_one, A, coeff_mk] <;>
      norm_num [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇]

end A285777Proof

open OMA.S_oeis_a285777 A285777Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a285777.main :=
  ⟨generating_function, even_value, odd_value, recurrence⟩
