import OMAStatements.S_oeis_a279873

/-!
The recurrence and generating function in OEIS A279873 give different values
for the twelfth coefficient after multiplying by the denominator.
Source: https://oeis.org/A279873
-/

open OMA.S_oeis_a279873 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a279873.main) := by
  rintro ⟨recurrence, generating⟩
  have hC (k : ℕ) : C (k : ℤ) = (k : ℤ⟦X⟧) := map_natCast C k
  have hc₁₀ : C (10 : ℤ) = (10 : ℤ⟦X⟧) := hC 10
  have hc₉₉ : C (99 : ℤ) = (99 : ℤ⟦X⟧) := hC 99
  have hc₁₀₀ : C (100 : ℤ) = (100 : ℤ⟦X⟧) := hC 100
  have hc₁₀₁ : C (101 : ℤ) = (101 : ℤ⟦X⟧) := hC 101
  have hc₁₁₀ : C (110 : ℤ) = (110 : ℤ⟦X⟧) := hC 110
  have hc₉₉₀ : C (990 : ℤ) = (990 : ℤ⟦X⟧) := hC 990
  have hc₁₀₀₀₀ : C (10000 : ℤ) = (10000 : ℤ⟦X⟧) := hC 10000
  have left :
      mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2)) =
        mk a - X ^ 2 * mk a - C 10000 * (X ^ 4 * mk a) + C 10000 * (X ^ 6 * mk a) := by
    rw [hc₁₀₀₀₀]
    ring
  have right :
      coeff 12 (1 + X + 100 * X ^ 2 + 110 * X ^ 3 - 101 * X ^ 4 + 100 * X ^ 6 +
        990 * X ^ 7 - 99 * X ^ 8 + 10 * X ^ 9 - X ^ 10 - 10000 * X ^ 12 + 10000 * X ^ 14 :
        ℤ⟦X⟧) = -10000 := by
    rw [← hc₁₀, ← hc₉₉, ← hc₁₀₀, ← hc₁₀₁, ← hc₁₁₀, ← hc₉₉₀, ← hc₁₀₀₀₀]
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]
    norm_num
  rw [left] at generating
  have hc := congrArg (coeff 12) generating
  rw [right] at hc
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul',
    if_pos (by decide : 2 ≤ (12 : ℕ)), if_pos (by decide : 4 ≤ (12 : ℕ)),
    if_pos (by decide : 6 ≤ (12 : ℕ)), Nat.reduceSub, coeff_mk] at hc
  have hr := recurrence 12 (by decide)
  norm_num only [Nat.reduceSub] at hr
  linarith
