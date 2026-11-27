import OMAStatements.S_oeis_a074359

namespace A074359Proof

open OMA.S_oeis_a074359 PowerSeries
open scoped PowerSeries

private noncomputable def c (b w : ℤ) (j n : ℕ) : ℤ := (nu b w n).coeff j

private noncomputable def series (b w : ℤ) (j : ℕ) : ℤ⟦X⟧ := mk (c b w j)

private noncomputable def d (b w : ℤ) : ℤ⟦X⟧ := 1 - C b * X - C w * X^2

private theorem step (b w : ℤ) (j n : ℕ) (hn : j ≤ n) :
    c b w j (n+2) = b * c b w j (n+1) + w * ∑ i ∈ Finset.range (j+1), c b w (j-i) n := by
  change (Polynomial.C b * nu b w (n+1) +
    Polynomial.C w * (∑ i ∈ Finset.range (n+1), Polynomial.X^i) * nu b w n).coeff j = _
  rw [mul_assoc (Polynomial.C w), Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  change b * c b w j (n+1) + w * _ = _
  apply congrArg (fun r : ℤ => b * c b w j (n+1) + w * r)
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hn
  simp [hi', c]

private theorem d_mul_coeff (b w : ℤ) (f : ℤ⟦X⟧) (n : ℕ) :
    coeff (n+2) (d b w * f) = coeff (n+2) f - b*coeff (n+1) f - w*coeff n f := by
  simp only [d, sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul,
    coeff_succ_X_mul, coeff_X_pow_mul]

private theorem coeff_X_mul_at (f : ℤ⟦X⟧) (n : ℕ) :
    coeff n (X*f) = if 1 ≤ n then coeff (n-1) f else 0 := by
  simpa using coeff_X_pow_mul' f 1 n

private theorem coeff_int_const (z : ℤ) (n : ℕ) :
    (z : Polynomial ℤ).coeff n = if n = 0 then z else 0 :=
  Polynomial.coeff_C

private theorem identities (b w : ℤ) :
    d b w * series b w 0 = 1 ∧
    d b w * series b w 1 = C w * (X^2 * (series b w 0 - 1)) ∧
    d b w * series b w 2 = C w * (X^2 * (series b w 1 + series b w 0 - 1 - C b * X)) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    ext n
    by_cases h : n < 4
    · interval_cases n <;>
        simp only [d, sub_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
          coeff_X_mul_at, coeff_X_pow_mul', coeff_one, series, coeff_mk, coeff_X] <;>
        norm_num [c, nu, Polynomial.coeff_one, coeff_int_const, Polynomial.coeff_X, Polynomial.coeff_X_pow,
          Polynomial.coeff_mul, Finset.sum_range_succ,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    · obtain ⟨k, rfl⟩ : ∃ k, n = (k + 2) + 2 := ⟨n-4, by omega⟩
      simp only [d_mul_coeff, coeff_C_mul, coeff_X_pow_mul, map_add, map_sub,
        series, coeff_mk, coeff_one, if_neg (show k+2 ≠ 0 by omega),
        if_neg (show k+2+2 ≠ 0 by omega), coeff_X,
        if_neg (show k+2 ≠ 1 by omega)]
      first
        | have hs := step b w 0 (k+2) (by omega)
          simp at hs
          linear_combination hs
        | have hs := step b w 1 (k+2) (by omega)
          norm_num [Finset.sum_range_succ] at hs
          linear_combination hs
        | have hs := step b w 2 (k+2) (by omega)
          norm_num [Finset.sum_range_succ] at hs
          linear_combination hs

private theorem series_two (b w : ℤ) :
    (d b w)^3 * series b w 2 = C w * X^2 *
      (C w * X^2 * (1-d b w) + d b w - (d b w)^2*(1+C b * X)) := by
  obtain ⟨h0, h1, h2⟩ := identities b w
  have h01 : (d b w)^2 * series b w 1 = C w * X^2 * (1-d b w) := by
    linear_combination (d b w)*h1 + C w * X^2 * h0
  linear_combination (d b w)^2*h2 + C w * X^2 * h01 + (C w * X^2 * d b w) * h0

theorem solve : type_of% @OMA.S_oeis_a074359.main := by
  change (2 * X^2 + 2 * X - 1 : ℤ⟦X⟧)^3 * series 2 2 2 =
    4 * X^4 * (-3 + 2*X + 8*X^2 + 4*X^3)
  have hd : d 2 2 = (1 - 2*X - 2*X^2 : ℤ⟦X⟧) := by simp [d]
  have h := series_two 2 2
  rw [hd] at h
  have hden : (2 * X^2 + 2 * X - 1 : ℤ⟦X⟧)^3 =
      -(1 - 2*X - 2*X^2)^3 := by ring
  rw [hden, neg_mul, h]
  norm_num
  ring

end A074359Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a074359.main := A074359Proof.solve
