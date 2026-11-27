import OMAStatements.S_oeis_a321225
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace A321225Proof

open OMA.S_oeis_a321225 PowerSeries

private theorem digit_period (n k : ℕ) : digit (n + 5*k) = digit n := by
  have h : (n+5*k)%5 = n%5 := by omega
  simp only [digit, h]

private theorem digit_pos (n : ℕ) : 0 < digit n := by
  unfold digit
  split <;> first | decide | (split <;> decide)

private theorem five_digit_sum (n : ℕ) :
    digit n + digit (n+1) + digit (n+2) + digit (n+3) + digit (n+4) = 9 := by
  have h : n % 5 < 5 := Nat.mod_lt _ (by decide)
  have h1 : (n+1)%5 = (n%5+1)%5 := by omega
  have h2 : (n+2)%5 = (n%5+2)%5 := by omega
  have h3 : (n+3)%5 = (n%5+3)%5 := by omega
  have h4 : (n+4)%5 = (n%5+4)%5 := by omega
  simp only [digit, h1, h2, h3, h4]
  generalize n%5 = i at h ⊢
  interval_cases i <;> decide

private theorem prefix_period (n : ℕ) : prefixSum (n + 5) = prefixSum n + 9 := by
  have h := five_digit_sum n
  change prefixSum n + digit n + digit (n+1) + digit (n+2) + digit (n+3) + digit (n+4) = _
  omega

private theorem prefix_period_mul (n k : ℕ) :
    prefixSum (n + 5*k) = prefixSum n + 9*k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : n + 5*(k+1) = (n+5*k)+5 := by omega
    rw [h, prefix_period, ih]
    omega

private theorem prefix_strict : StrictMono prefixSum := by
  apply strictMono_nat_of_lt_succ
  intro n
  change prefixSum n < prefixSum n + digit n
  exact Nat.lt_add_of_pos_right (digit_pos n)

private theorem triangle_next (n : ℕ) : triangle (n+1) = triangle n + n+1 := by
  unfold triangle
  have h : (n+1)*(n+1+1) = n*(n+1)+2*(n+1) := by ring
  rw [h]
  omega

private theorem triangle_shift (n : ℕ) : triangle (n+9) = triangle n + 9*(n+5) := by
  unfold triangle
  have h : (n+9)*(n+9+1) = n*(n+1)+2*(9*(n+5)) := by ring
  rw [h]
  omega

private theorem known_residue (n : ℕ) :
    triangle n % 9 = 0 ∨ triangle n % 9 = 1 ∨
      triangle n % 9 = 3 ∨ triangle n % 9 = 6 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 9
    · interval_cases n <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, n = k+9 := ⟨n-9, by omega⟩
      rw [triangle_shift]
      have he : (triangle k + 9*(k+5)) % 9 = triangle k % 9 := by omega
      rw [he]
      exact ih k (by omega)

private def offset (r : ℕ) : ℕ :=
  if r = 0 then 0 else if r = 1 then 1 else if r = 3 then 2 else 3

private def explicitCut (n : ℕ) : ℕ :=
  offset (triangle n % 9) + 5 * (triangle n / 9)

private theorem explicit_cut_spec (n : ℕ) : prefixSum (explicitCut n) = triangle n := by
  rw [explicitCut, prefix_period_mul]
  have h : prefixSum (offset (triangle n % 9)) = triangle n % 9 := by
    rcases known_residue n with h | h | h | h <;> rw [h] <;> decide
  rw [h]
  omega

private theorem cut_eq (n : ℕ) : cut n = explicitCut n := by
  have h : {k : ℕ | prefixSum k = triangle n} = {explicitCut n} := by
    ext k
    change prefixSum k = triangle n ↔ k = explicitCut n
    rw [← explicit_cut_spec n]
    exact prefix_strict.injective.eq_iff
  rw [cut, h, csInf_singleton]

private theorem cut_spec (n : ℕ) : prefixSum (cut n) = triangle n := by
  rw [cut_eq, explicit_cut_spec]

private theorem cut_shift (n : ℕ) : cut (n+9) = cut n + 5*(n+5) := by
  apply prefix_strict.injective
  rw [prefix_period_mul, cut_spec, cut_spec, triangle_shift]

private theorem cut_mono (n : ℕ) : cut n ≤ cut (n+1) := by
  apply prefix_strict.le_iff_le.mp
  rw [cut_spec, cut_spec, triangle_next]
  omega

private theorem decimal_start_shift (start k len : ℕ) :
    decimal (start + 5*k) len = decimal start len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    simp only [decimal, ih]
    rw [show start + 5*k + len = (start+len)+5*k by omega, digit_period]

private theorem decimal_append (start len suffix : ℕ) :
    decimal start (len+suffix) = 10^suffix * decimal start len + decimal (start+len) suffix := by
  induction suffix with
  | zero => simp [decimal]
  | succ suffix ih =>
    change 10*decimal start (len+suffix) + (digit (start+(len+suffix)) : ℤ) =
      10^(suffix+1)*decimal start len +
        (10*decimal (start+len) suffix + (digit (start+len+suffix) : ℤ))
    rw [ih, pow_succ, show start+(len+suffix) = start+len+suffix by omega]
    ring

private theorem append_chunk (n : ℕ) :
    a (n+1+9) = 100000*a (n+1) + decimal (cut (n+1)) 5 := by
  change decimal (cut (n+9)) (cut (n+1+9) - cut (n+9)) = _
  have h : cut (n+1+9) - cut (n+9) = cut (n+1) - cut n + 5 := by
    rw [cut_shift (n+1), cut_shift n]
    have hb := cut_mono n
    omega
  rw [h, cut_shift n, decimal_start_shift, decimal_append]
  simp only [a]
  rw [Nat.add_sub_of_le (cut_mono n)]
  norm_num

private theorem recurrence (n : ℕ) (hn : 18 < n) :
    a n = 100001*a (n-9) - 100000*a (n-18) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+1+18 := ⟨n-19, by omega⟩
  have h0 := append_chunk k
  have h1 := append_chunk (k+9)
  rw [show k+9+1+9 = k+1+18 by omega, show k+9+1 = k+1+9 by omega,
    cut_shift (k+1), decimal_start_shift] at h1
  rw [show k+1+18-9 = k+1+9 by omega, show k+1+18-18 = k+1 by omega]
  omega

private def computableA : ℕ → ℤ
  | 0 => 0
  | n + 1 => decimal (explicitCut n) (explicitCut (n+1) - explicitCut n)

private theorem a_eval (n : ℕ) : a n = computableA n := by
  cases n <;> simp only [a, computableA, cut_eq]

private theorem gf :
    (100000*X^18 - 100001*X^9 + 1 : ℤ⟦X⟧) * mk a =
      X*(10000*X^16 + 20000*X^15 + 30000*X^14 + 21100*X^13 + 23000*X^12
        + 21120*X^11 + 32110*X^10 + 23210*X^9 + 12321*X^8 + 2321*X^7
        + 3211*X^6 + 2112*X^5 + 23*X^4 + 211*X^3 + 3*X^2 + 2*X + 1) := by
  have hDen : (100000*X^18 - 100001*X^9 + 1 : ℤ⟦X⟧) =
      C 100000*X^18 - C 100001*X^9 + 1 := by norm_num
  have hNum :
      (X*(10000*X^16 + 20000*X^15 + 30000*X^14 + 21100*X^13 + 23000*X^12
        + 21120*X^11 + 32110*X^10 + 23210*X^9 + 12321*X^8 + 2321*X^7
        + 3211*X^6 + 2112*X^5 + 23*X^4 + 211*X^3 + 3*X^2 + 2*X + 1) : ℤ⟦X⟧) =
      C 10000*X^17 + C 20000*X^16 + C 30000*X^15 + C 21100*X^14
      + C 23000*X^13 + C 21120*X^12 + C 32110*X^11 + C 23210*X^10
      + C 12321*X^9 + C 2321*X^8 + C 3211*X^7 + C 2112*X^6 + C 23*X^5
      + C 211*X^4 + C 3*X^3 + C 2*X^2 + X := by norm_num; ring
  rw [hDen, hNum]
  ext n
  simp only [add_mul, sub_mul, mul_assoc, one_mul, map_add, map_sub,
    coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_X, coeff_mk]
  by_cases hn : n < 19
  · simp only [a_eval]
    interval_cases n <;> decide
  · simp only [if_pos (show 18 ≤ n by omega), if_pos (show 9 ≤ n by omega),
      if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega), if_neg (show n ≠ 8 by omega), if_neg (show n ≠ 9 by omega),
      if_neg (show n ≠ 10 by omega), if_neg (show n ≠ 11 by omega), if_neg (show n ≠ 12 by omega),
      if_neg (show n ≠ 13 by omega), if_neg (show n ≠ 14 by omega), if_neg (show n ≠ 15 by omega),
      if_neg (show n ≠ 16 by omega), if_neg (show n ≠ 17 by omega)]
    have h := recurrence n (by omega)
    omega

end A321225Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a321225.main :=
  ⟨A321225Proof.recurrence, A321225Proof.gf⟩
