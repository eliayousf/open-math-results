import OMAStatements.S_oeis_a283646

open OMA.S_oeis_a283646 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a283646.main) := by
  rintro ⟨generating, recurrence⟩
  have hC (k : ℕ) : C (k : ℤ) = (k : ℤ⟦X⟧) := map_natCast C k
  have hC₃ : C (3 : ℤ) = (3 : ℤ⟦X⟧) := hC 3
  have hC₄ : C (4 : ℤ) = (4 : ℤ⟦X⟧) := hC 4
  have hC₁₀ : C (10 : ℤ) = (10 : ℤ⟦X⟧) := hC 10
  have hC₁₆ : C (16 : ℤ) = (16 : ℤ⟦X⟧) := hC 16
  have hC₄₀ : C (40 : ℤ) = (40 : ℤ⟦X⟧) := hC 40
  have hC₇₂ : C (72 : ℤ) = (72 : ℤ⟦X⟧) := hC 72
  have hC₁₂₈ : C (128 : ℤ) = (128 : ℤ⟦X⟧) := hC 128
  have hC₁₅₂ : C (152 : ℤ) = (152 : ℤ⟦X⟧) := hC 152
  have hC₂₅₆ : C (256 : ℤ) = (256 : ℤ⟦X⟧) := hC 256
  have left :
      mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) *
        (1 + 16 * X ^ 4)) =
        mk a - X ^ 2 * mk a - C 256 * (X ^ 8 * mk a) + C 256 * (X ^ 10 * mk a) := by
    rw [hC₂₅₆]
    ring
  have right :
      coeff 15 (1 + 3 * X + 4 * X ^ 2 + 10 * X ^ 3 + 16 * X ^ 4 + 40 * X ^ 5 +
        72 * X ^ 6 + 152 * X ^ 7 - 128 * X ^ 9 + 128 * X ^ 10 -
        128 * X ^ 11 + 256 * X ^ 15 : ℤ⟦X⟧) = 256 := by
    rw [← hC₃, ← hC₄, ← hC₁₀, ← hC₁₆, ← hC₄₀, ← hC₇₂, ← hC₁₂₈, ← hC₁₅₂, ← hC₂₅₆]
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]
    norm_num
  rw [left] at generating
  have hc := congrArg (coeff 15) generating
  rw [right] at hc
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul',
    if_pos (by decide : 2 ≤ (15 : ℕ)), if_pos (by decide : 8 ≤ (15 : ℕ)),
    if_pos (by decide : 10 ≤ (15 : ℕ)), Nat.reduceSub, coeff_mk] at hc
  have hr := recurrence 15 (by decide)
  norm_num only [Nat.reduceSub] at hr
  linarith
