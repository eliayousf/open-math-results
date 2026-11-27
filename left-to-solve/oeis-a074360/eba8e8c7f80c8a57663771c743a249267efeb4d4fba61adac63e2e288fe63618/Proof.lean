import OMAStatements.S_oeis_a074360

namespace A074360Proof

open OMA.S_oeis_a074360
open PowerSeries
open scoped PowerSeries

private noncomputable def c (j n : ℕ) : ℤ := (nu n).coeff j

private noncomputable def series (j : ℕ) : ℤ⟦X⟧ := mk (c j)

private noncomputable def d : ℤ⟦X⟧ := 1 - C 2 * X - C 2 * X^2

private theorem step (j n : ℕ) (hn : j ≤ n) :
    c j (n+2) = 2 * c j (n+1) + 2 * ∑ i ∈ Finset.range (j+1), c (j-i) n := by
  have htwo : (2 : Polynomial ℤ) = Polynomial.C 2 := by norm_num
  change (2 * nu (n+1) + 2 * (∑ i ∈ Finset.range (n+1), Polynomial.X^i) * nu n).coeff j = _
  rw [mul_assoc (2 : Polynomial ℤ), htwo, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  change 2 * c j (n+1) + 2 * _ = _
  apply congrArg (fun b : ℤ => 2 * c j (n+1) + 2 * b)
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hn
  simp [hi', c]

private theorem d_mul_coeff (f : ℤ⟦X⟧) (n : ℕ) :
    coeff (n+2) (d*f) = coeff (n+2) f - 2*coeff (n+1) f - 2*coeff n f := by
  simp only [d, sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul,
    coeff_succ_X_mul, coeff_X_pow_mul]

private theorem coeff_X_mul_at (f : ℤ⟦X⟧) (n : ℕ) :
    coeff n (X*f) = if 1 ≤ n then coeff (n-1) f else 0 := by
  simpa using coeff_X_pow_mul' f 1 n

private theorem identities :
    d * series 0 = 1 ∧
    d * series 1 = C 2 * (X^2 * (series 0 - 1)) ∧
    d * series 2 = C 2 * (X^2 * (series 1 + series 0 - 1 - C 2 * X)) ∧
    d * series 3 = C 2 * (X^2 * (series 2 + series 1 + series 0 - 1 - C 2 * X - C 6 * X^2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    ext n
    by_cases h : n < 5
    · interval_cases n <;>
        simp only [d, sub_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
          coeff_X_mul_at, coeff_X_pow_mul', coeff_one, series, coeff_mk, coeff_X, coeff_X_pow] <;>
        norm_num [c, nu, Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow,
          Polynomial.coeff_mul, Finset.sum_range_succ,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    · obtain ⟨k, rfl⟩ : ∃ k, n = (k + 3) + 2 := ⟨n-5, by omega⟩
      simp only [d_mul_coeff, coeff_C_mul, coeff_X_pow_mul, map_add, map_sub,
        series, coeff_mk, coeff_one, if_neg (show k+3 ≠ 0 by omega),
        if_neg (show k+3+2 ≠ 0 by omega), coeff_X, coeff_X_pow,
        if_neg (show k+3 ≠ 1 by omega), if_neg (show k+3 ≠ 2 by omega)]
      first
        | have hs := step 0 (k+3) (by omega)
          simp at hs
          omega
        | have hs := step 1 (k+3) (by omega)
          norm_num [Finset.sum_range_succ] at hs
          omega
        | have hs := step 2 (k+3) (by omega)
          norm_num [Finset.sum_range_succ] at hs
          omega
        | have hs := step 3 (k+3) (by omega)
          norm_num [Finset.sum_range_succ] at hs
          omega

theorem solve : type_of% @OMA.S_oeis_a074360.main := by
  change (2 * X^2 + 2 * X - 1 : ℤ⟦X⟧)^4 * series 3 =
    8*X^5*(1+X)*(12*X^4 + 24*X^3 - 2*X^2 - 16*X + 5)
  obtain ⟨h0, h1, h2, h3⟩ := identities
  have hc2 : (C 2 : ℤ⟦X⟧) = 2 := by norm_num
  have hc6 : (C 6 : ℤ⟦X⟧) = 6 := by norm_num
  simp only [hc2, hc6] at h1 h2 h3
  have hd : d = 1 - 2*X - 2*X^2 := by simp [d]
  have hden : (2 * X^2 + 2 * X - 1 : ℤ⟦X⟧)^4 = d^4 := by rw [hd]; ring
  rw [hden]
  have h01 : d^2 * series 1 = 2*X^2*(1-d) := by
    linear_combination d*h1 + 2*X^2*h0
  have h02 : d^3 * series 2 = 2*X^2*(2*X^2*(1-d)+d-d^2*(1+2*X)) := by
    linear_combination d^2*h2 + 2*X^2*h01 + (2*X^2*d)*h0
  have h03 : d^4 * series 3 =
      2*X^2*(2*X^2*(2*X^2*(1-d)+d-d^2*(1+2*X)) +
        d*2*X^2*(1-d) + d^2-d^3*(1+2*X+6*X^2)) := by
    linear_combination d^3*h3 + 2*X^2*h02 + (2*X^2*d)*h01 + (2*X^2*d^2)*h0
  rw [h03, hd]
  ring

end A074360Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a074360.main := A074360Proof.solve
