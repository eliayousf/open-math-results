import OMAStatements.S_oeis_a284482

open OMA.S_oeis_a284482 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284482.main) := by
  rintro ⟨generating, recurrence⟩
  have hC (k : ℕ) : C (k : ℤ) = (k : ℤ⟦X⟧) := map_natCast C k
  have hC₂ : C (2 : ℤ) = (2 : ℤ⟦X⟧) := hC 2
  have hC₄ : C (4 : ℤ) = (4 : ℤ⟦X⟧) := hC 4
  have hC₅ : C (5 : ℤ) = (5 : ℤ⟦X⟧) := hC 5
  have hC₈ : C (8 : ℤ) = (8 : ℤ⟦X⟧) := hC 8
  have hC₁₆ : C (16 : ℤ) = (16 : ℤ⟦X⟧) := hC 16
  have left :
      mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + X ^ 2)) =
        mk a - C 2 * (X ^ 1 * mk a) - X ^ 4 * mk a + C 2 * (X ^ 5 * mk a) := by
    rw [hC₂]
    ring
  have right :
      coeff 7 (1 + X - X ^ 2 + 5 * X ^ 3 - 2 * X ^ 4 +
        4 * X ^ 5 - 8 * X ^ 7 + 16 * X ^ 8 : ℤ⟦X⟧) = -8 := by
    rw [← hC₂, ← hC₄, ← hC₅, ← hC₈, ← hC₁₆]
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
