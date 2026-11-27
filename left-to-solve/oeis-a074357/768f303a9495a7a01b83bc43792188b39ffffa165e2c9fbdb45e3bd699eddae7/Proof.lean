import OMAStatements.S_oeis_a074357

namespace A074357Proof

open OMA.S_oeis_a074357
open PowerSeries
open scoped PowerSeries

private noncomputable def c (j n : ℕ) : ℤ := (nu 1 3 n).coeff j

private noncomputable def series (j : ℕ) : ℤ⟦X⟧ := mk (c j)

private noncomputable def d : ℤ⟦X⟧ := 1 - C 1 * X - C 3 * X^2

private theorem step (j n : ℕ) (hn : j ≤ n) :
    c j (n+2) = 1 * c j (n+1) + 3 * ∑ i ∈ Finset.range (j+1), c (j-i) n := by
  change (Polynomial.C 1 * nu 1 3 (n+1) +
    Polynomial.C 3 * (∑ i ∈ Finset.range (n+1), Polynomial.X^i) * nu 1 3 n).coeff j = _
  rw [mul_assoc (Polynomial.C 3), Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  change 1 * c j (n+1) + 3 * _ = _
  apply congrArg (fun b : ℤ => 1 * c j (n+1) + 3 * b)
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hn
  simp [hi', c]

private theorem d_mul_coeff (f : ℤ⟦X⟧) (n : ℕ) :
    coeff (n+2) (d*f) = coeff (n+2) f - 1*coeff (n+1) f - 3*coeff n f := by
  simp only [d, sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul,
    coeff_succ_X_mul, coeff_X_pow_mul]

private theorem coeff_X_mul_at (f : ℤ⟦X⟧) (n : ℕ) :
    coeff n (X*f) = if 1 ≤ n then coeff (n-1) f else 0 := by
  simpa using coeff_X_pow_mul' f 1 n

private theorem identities :
    d * series 0 = 1 ∧
    d * series 1 = C 3 * (X^2 * (series 0 - 1)) ∧
    d * series 2 = C 3 * (X^2 * (series 1 + series 0 - 1 - C 1 * X)) ∧
    d * series 3 = C 3 * (X^2 * (series 2 + series 1 + series 0 - 1 - C 1 * X - C 4 * X^2)) := by
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

theorem solve : type_of% @OMA.S_oeis_a074357.main := by
  change (3*X^2+X-1 : ℤ⟦X⟧)^4 * series 3 =
    3*X^5*(3*X+1)*(36*X^4+24*X^3-29*X^2-14*X+10)
  obtain ⟨h0, h1, h2, h3⟩ := identities
  have hc1 : (C 1 : ℤ⟦X⟧) = 1 := by norm_num
  have hc3 : (C 3 : ℤ⟦X⟧) = 3 := by norm_num
  have hc4 : (C 4 : ℤ⟦X⟧) = 4 := by norm_num
  simp only [hc1, hc3, hc4, one_mul] at h1 h2 h3
  have hd : d = 1 - X - 3*X^2 := by simp [d]
  have hden : (3*X^2+X-1 : ℤ⟦X⟧)^4 = d^4 := by rw [hd]; ring
  rw [hden]
  have h01 : d^2 * series 1 = 3*X^2*(1-d) := by
    linear_combination d*h1 + 3*X^2*h0
  have h02 : d^3 * series 2 = 3*X^2*(3*X^2*(1-d)+d-d^2*(1+X)) := by
    linear_combination d^2*h2 + 3*X^2*h01 + (3*X^2*d)*h0
  have h03 : d^4 * series 3 =
      3*X^2*(3*X^2*(3*X^2*(1-d)+d-d^2*(1+X)) +
        d*3*X^2*(1-d) + d^2-d^3*(1+X+4*X^2)) := by
    linear_combination d^3*h3 + 3*X^2*h02 + (3*X^2*d)*h01 + (3*X^2*d^2)*h0
  rw [h03, hd]
  ring

end A074357Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a074357.main := A074357Proof.solve
