import OMAStatements.S_oeis_a074356

namespace A074356Proof

open OMA.S_oeis_a074356 PowerSeries
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

private theorem gf : (1-X-3*X^2 : ℤ⟦X⟧)^3 * mk a = 3*X^4*(2-3*X)*(2+4*X+3*X^2) := by
  change (1-X-3*X^2 : ℤ⟦X⟧)^3 * series 1 3 2 = _
  have hd : d 1 3 = (1-X-3*X^2 : ℤ⟦X⟧) := by simp [d]
  rw [← hd, series_two, hd]
  norm_num
  ring

private theorem recurrence (n : ℕ) (hn : 7 < n) :
    a n = 3*a (n-1) + 6*a (n-2) - 17*a (n-3) - 18*a (n-4) + 27*a (n-5) + 27*a (n-6) := by
  have hDen : (1-X-3*X^2 : ℤ⟦X⟧)^3 =
      1 - C 3 * X^1 - C 6 * X^2 + C 17 * X^3 + C 18 * X^4 - C 27 * X^5 - C 27 * X^6 := by
    norm_num
    ring
  have hNum : (3*X^4*(2-3*X)*(2+4*X+3*X^2) : ℤ⟦X⟧) =
      C 12 * X^4 + C 6 * X^5 - C 18 * X^6 - C 27 * X^7 := by
    norm_num
    ring
  have h := gf
  rw [hDen, hNum] at h
  have h := congrArg (coeff n) h
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow,
    if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega),
    if_pos (show 4 ≤ n by omega), if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega),
    if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega),
    if_neg (show n ≠ 6 by omega), if_neg (show n ≠ 7 by omega)] at h
  omega

end A074356Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a074356.main :=
  ⟨A074356Proof.gf, A074356Proof.recurrence⟩
