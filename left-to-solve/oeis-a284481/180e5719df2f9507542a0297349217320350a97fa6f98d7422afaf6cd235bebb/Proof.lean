import OMAStatements.S_oeis_a284481

open OMA.S_oeis_a284481 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284481.main) := by
  rintro ⟨generating, recurrence⟩
  have hC (k : ℕ) : C (k : ℤ) = (k : ℤ⟦X⟧) := map_natCast C k
  have hC₂ : C (2 : ℤ) = (2 : ℤ⟦X⟧) := hC 2
  have hC₈ : C (8 : ℤ) = (8 : ℤ⟦X⟧) := hC 8
  have hC₁₀ : C (10 : ℤ) = (10 : ℤ⟦X⟧) := hC 10
  have hC₁₆ : C (16 : ℤ) = (16 : ℤ⟦X⟧) := hC 16
  have left :
      mk a * ((1 - X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2)) =
        mk a - X ^ 1 * mk a - C 16 * (X ^ 4 * mk a) + C 16 * (X ^ 5 * mk a) := by
    rw [hC₁₆]
    ring
  have right :
      coeff 7 (1 + 2 * X + 2 * X ^ 2 + 10 * X ^ 3 - 8 * X ^ 4 +
        8 * X ^ 5 - 16 * X ^ 7 + 16 * X ^ 8 : ℤ⟦X⟧) = -16 := by
    rw [← hC₂, ← hC₈, ← hC₁₀, ← hC₁₆]
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]
    norm_num
  rw [left] at generating
  have hc := congrArg (coeff 7) generating
  rw [right] at hc
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul',
    if_pos (by decide : 1 ≤ (7 : ℕ)), if_pos (by decide : 4 ≤ (7 : ℕ)),
    if_pos (by decide : 5 ≤ (7 : ℕ)), Nat.reduceSub, coeff_mk] at hc
  have hr := recurrence 7 (by decide)
  norm_num only [Nat.reduceSub] at hr
  linarith
