import OMAStatements.S_oeis_a074354
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

namespace A074354Proof

open OMA.S_oeis_a074354
open PowerSeries
open scoped PowerSeries

private noncomputable def c (j n : ℕ) : ℤ := (nu 1 2 n).coeff j

private noncomputable def series (j : ℕ) : ℤ⟦X⟧ := mk (c j)

private noncomputable def d : ℤ⟦X⟧ := 1 - C 1 * X - C 2 * X^2

private theorem step (j n : ℕ) (hn : j ≤ n) :
    c j (n+2) = 1 * c j (n+1) + 2 * ∑ i ∈ Finset.range (j+1), c (j-i) n := by
  change (Polynomial.C 1 * nu 1 2 (n+1) +
    Polynomial.C 2 * (∑ i ∈ Finset.range (n+1), Polynomial.X^i) * nu 1 2 n).coeff j = _
  rw [mul_assoc (Polynomial.C 2), Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  change 1 * c j (n+1) + 2 * _ = _
  apply congrArg (fun b : ℤ => 1 * c j (n+1) + 2 * b)
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hn
  simp [hi', c]

private theorem d_mul_coeff (f : ℤ⟦X⟧) (n : ℕ) :
    coeff (n+2) (d*f) = coeff (n+2) f - 1*coeff (n+1) f - 2*coeff n f := by
  simp only [d, sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul,
    coeff_succ_X_mul, coeff_X_pow_mul]

private theorem coeff_X_mul_at (f : ℤ⟦X⟧) (n : ℕ) :
    coeff n (X*f) = if 1 ≤ n then coeff (n-1) f else 0 := by
  simpa using coeff_X_pow_mul' f 1 n

private theorem identities :
    d * series 0 = 1 ∧
    d * series 1 = C 2 * (X^2 * (series 0 - 1)) ∧
    d * series 2 = C 2 * (X^2 * (series 1 + series 0 - 1 - C 1 * X)) ∧
    d * series 3 = C 2 * (X^2 * (series 2 + series 1 + series 0 - 1 - C 1 * X - C 3 * X^2)) := by
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

private theorem gf : ((1+X)^4 * (1-2*X)^4 : ℤ⟦X⟧) * mk a =
    2*X^5*(1+2*X)*(7-10*X-13*X^2+12*X^3+12*X^4) := by
  change ((1+X)^4 * (1-2*X)^4 : ℤ⟦X⟧) * series 3 = _
  obtain ⟨h0, h1, h2, h3⟩ := identities
  have hc1 : (C 1 : ℤ⟦X⟧) = 1 := by norm_num
  have hc2 : (C 2 : ℤ⟦X⟧) = 2 := by norm_num
  have hc3 : (C 3 : ℤ⟦X⟧) = 3 := by norm_num
  simp only [hc1, hc2, hc3, one_mul] at h1 h2 h3
  have hd : d = 1 - X - 2*X^2 := by simp [d]
  have hden : ((1+X)^4 * (1-2*X)^4 : ℤ⟦X⟧) = d^4 := by rw [hd]; ring
  rw [hden]
  have h01 : d^2 * series 1 = 2*X^2*(1-d) := by
    linear_combination d*h1 + 2*X^2*h0
  have h02 : d^3 * series 2 = 2*X^2*(2*X^2*(1-d)+d-d^2*(1+X)) := by
    linear_combination d^2*h2 + 2*X^2*h01 + (2*X^2*d)*h0
  have h03 : d^4 * series 3 =
      2*X^2*(2*X^2*(2*X^2*(1-d)+d-d^2*(1+X)) +
        d*2*X^2*(1-d) + d^2-d^3*(1+X+3*X^2)) := by
    linear_combination d^3*h3 + 2*X^2*h02 + (2*X^2*d)*h01 + (2*X^2*d^2)*h0
  rw [h03, hd]
  ring

private theorem recurrence (n : ℕ) (hn : 10 < n) :
    a n = 4*a (n-1) + 2*a (n-2) - 20*a (n-3) - a (n-4) +
      40*a (n-5) + 8*a (n-6) - 32*a (n-7) - 16*a (n-8) := by
  have hDen : ((1+X)^4 * (1-2*X)^4 : ℤ⟦X⟧) =
      1 - C 4 * X^1 - C 2 * X^2 + C 20 * X^3 + X^4
        - C 40 * X^5 - C 8 * X^6 + C 32 * X^7 + C 16 * X^8 := by
    norm_num
    ring
  have hNum : (2*X^5*(1+2*X)*(7-10*X-13*X^2+12*X^3+12*X^4) : ℤ⟦X⟧) =
      C 14 * X^5 + C 8 * X^6 - C 66 * X^7 - C 28 * X^8 + C 72 * X^9 + C 48 * X^10 := by
    norm_num
    ring
  have h := gf
  rw [hDen, hNum] at h
  have h := congrArg (coeff n) h
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow,
    if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega),
    if_pos (show 4 ≤ n by omega), if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega),
    if_pos (show 7 ≤ n by omega), if_pos (show 8 ≤ n by omega),
    if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega),
    if_neg (show n ≠ 7 by omega), if_neg (show n ≠ 8 by omega),
    if_neg (show n ≠ 9 by omega), if_neg (show n ≠ 10 by omega)] at h
  omega

end A074354Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a074354.main :=
  ⟨A074354Proof.gf, A074354Proof.recurrence⟩
