import OMAStatements.S_oeis_a000033
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! The factorial truncates the sum modulo the prime. The surviving binomial
coefficients have zero second difference by the polynomial identity in prime
characteristic. The prime 2 follows from the period-four parity formula. -/

open Finset Polynomial OMA.S_oeis_a000033

private theorem rookCount_eq_zero {n r : ℕ} (h : n < r) :
    rookCount n r = 0 := by
  unfold rookCount
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]

private theorem sum_range_of_vanishing_tail {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) {m n : ℕ} (hm : ∀ r, m ≤ r → f r = 0) (hn : ∀ r, n ≤ r → f r = 0) :
    (∑ r ∈ range m, f r) = ∑ r ∈ range n, f r := by
  have extend {k : ℕ} (hk : k ≤ max m n) (hz : ∀ r, k ≤ r → f r = 0) :
      (∑ r ∈ range k, f r) = ∑ r ∈ range (max m n), f r := by
    apply sum_subset (range_mono hk)
    intro r _ hr
    exact hz r (Nat.le_of_not_lt fun h => hr (mem_range.mpr h))
  exact (extend (le_max_left _ _) hm).trans (extend (le_max_right _ _) hn).symm

private theorem signedValue_mod (n p : ℕ) (hp : 0 < p) :
    (signedValue n : ZMod p) = ∑ r ∈ range p, (signedTerm n r : ZMod p) := by
  rw [signedValue, Int.cast_sum]
  apply sum_range_of_vanishing_tail
  · intro r hr
    simp [signedTerm, rookCount_eq_zero (by omega : n < r)]
  · intro r hr
    have hd := Nat.dvd_factorial hp hr
    have hz : (r.factorial : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
    simp [signedTerm, hz]

private theorem choose_two_step (m : ℕ) : (m + 1).choose 2 = m + m.choose 2 := by
  simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' m 1

private theorem twice_choose_two (m : ℕ) :
    (2 : ℤ) * (m.choose 2 : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
  cases m with
  | zero => norm_num
  | succ m =>
    have h := congrArg (fun t : ℕ => (t : ℤ)) (Nat.add_one_mul_choose_eq m 1)
    simp only [Nat.choose_one_right, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    linear_combination -h

private theorem twice_signedTerm (p n r : ℕ) :
    (2 : ZMod p) * (signedTerm n r : ZMod p) =
      (-1 : ZMod p) ^ r * r.factorial * ((n : ZMod p) - r) *
        ((n : ZMod p) - r - 1) * rookCount n r := by
  by_cases hr : r ≤ n
  · have h := congrArg (fun z : ℤ => (z : ZMod p)) (twice_choose_two (n - r))
    push_cast [Nat.cast_sub hr] at h
    simp only [signedTerm, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    linear_combination ((-1 : ZMod p) ^ r * r.factorial * rookCount n r) * h
  · simp [signedTerm, rookCount_eq_zero (Nat.lt_of_not_ge hr)]

private theorem choose_second_difference (p : ℕ) [Fact p.Prime] (m k : ℕ) (hk : k < 2 * p) :
    ((m + 2 * p).choose k : ZMod p) - 2 * ((m + p).choose k : ZMod p) +
      (m.choose k : ZMod p) = 0 := by
  let q : (ZMod p)[X] := 1 + X
  have hf : q ^ p = 1 + X ^ p := by
    dsimp [q]
    rw [add_pow_char _ _ p, one_pow]
  have hpoly : q ^ (m + 2 * p) - (q ^ (m + p) + q ^ (m + p)) + q ^ m =
      q ^ m * X ^ (2 * p) := by
    calc
      _ = q ^ m * (q ^ p - 1) ^ 2 := by
        rw [show m + 2 * p = m + p + p by omega]
        simp only [pow_add]
        ring
      _ = _ := by rw [hf, add_sub_cancel_left, ← pow_mul, Nat.mul_comm p]
  have hc := congrArg (fun f : (ZMod p)[X] => f.coeff k) hpoly
  simp only [coeff_add, coeff_sub, coeff_mul_X_pow', if_neg (Nat.not_le_of_lt hk), q,
    coeff_one_add_X_pow] at hc
  simpa only [two_mul] using hc

private theorem rook_second_difference (p : ℕ) [Fact p.Prime] {n r : ℕ}
    (hn : 0 < n) (hr : r < p) :
    (rookCount (n + 2 * p) r : ZMod p) - 2 * (rookCount (n + p) r : ZMod p) +
      (rookCount n r : ZMod p) = 0 := by
  have h₁ := choose_second_difference p (n + r) (2 * r) (by omega)
  have h₂ := choose_second_difference p (n + r - 1) (2 * r) (by omega)
  simp only [rookCount, Nat.cast_add]
  rw [show n + 2 * p + r = n + r + 2 * p by omega,
      show n + p + r = n + r + p by omega,
      show n + r + 2 * p - 1 = n + r - 1 + 2 * p by omega,
      show n + r + p - 1 = n + r - 1 + p by omega]
  linear_combination h₁ + h₂

private theorem signedTerm_second_difference (p : ℕ) [Fact p.Prime] {n r : ℕ}
    (hn : 0 < n) (hr : r < p) :
    (2 : ZMod p) * ((signedTerm (n + 2 * p) r : ZMod p) -
      2 * (signedTerm (n + p) r : ZMod p) + (signedTerm n r : ZMod p)) = 0 := by
  rw [mul_add, mul_sub, mul_left_comm (2 : ZMod p), twice_signedTerm, twice_signedTerm,
    twice_signedTerm]
  push_cast
  simp only [ZMod.natCast_self, mul_zero, add_zero]
  linear_combination
    ((-1 : ZMod p) ^ r * r.factorial * ((n : ZMod p) - r) *
      ((n : ZMod p) - r - 1)) * rook_second_difference p hn hr

private theorem signedValue_second_difference (p : ℕ) [Fact p.Prime] {n : ℕ}
    (hn : 0 < n) (hodd : p ≠ 2) :
    (signedValue (n + 2 * p) : ZMod p) - 2 * (signedValue (n + p) : ZMod p) +
      (signedValue n : ZMod p) = 0 := by
  have hp : p.Prime := Fact.out
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
    have hge := hp.two_le
    omega
  apply (mul_eq_zero.mp ?_).resolve_left htwo
  rw [signedValue_mod _ _ hp.pos, signedValue_mod _ _ hp.pos, signedValue_mod _ _ hp.pos,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  exact sum_eq_zero fun r hr => signedTerm_second_difference p hn (mem_range.mp hr)

private theorem a_mod_two (n : ℕ) :
    (a n : ZMod 2) = (n : ZMod 2) * ((n - 1).choose 2 : ZMod 2) := by
  have hneg : (-1 : ZMod 2) = 1 := by decide
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hR : rookCount n 1 = n + 2 * n.choose 2 := by
    simp only [rookCount, Nat.mul_one, Nat.add_sub_cancel, choose_two_step]
    omega
  rw [a, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, hneg, one_pow, one_mul,
    signedValue_mod _ _ (by decide)]
  rw [show range 2 = {0, 1} by decide, sum_insert (by decide), sum_singleton]
  have hR₀ : rookCount n 0 = 2 := by simp [rookCount]
  simp [signedTerm, hR₀, hR, htwo, Nat.factorial, mul_comm]

private theorem a_period_four (n : ℕ) (hn : 0 < n) :
    (a (n + 4) : ZMod 2) = (a n : ZMod 2) := by
  have hfour : (4 : ZMod 2) = 0 := by decide
  have hshift (m : ℕ) : (m + 4).choose 2 = m.choose 2 + 4 * m + 6 := by
    calc
      _ = (m + 3) + (m + 3).choose 2 := choose_two_step _
      _ = _ := by
        rw [show (m + 3).choose 2 = (m + 2) + (m + 2).choose 2 from choose_two_step _,
          show (m + 2).choose 2 = (m + 1) + (m + 1).choose 2 from choose_two_step _, choose_two_step]
        omega
  rw [a_mod_two, a_mod_two, show n + 4 - 1 = (n - 1) + 4 by omega, hshift]
  push_cast
  simp only [hfour, show (6 : ZMod 2) = 0 by decide, zero_mul, add_zero]

/-- Van Hoeij's congruence conjecture for A000033. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a000033.main := by
  intro n p hn hp
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
  push_cast
  by_cases h : p = 2
  · subst p
    change (a n : ZMod 2) + 2 * (a (n + 2) : ZMod 2) + (a (n + 4) : ZMod 2) = 0
    rw [a_period_four n hn, show (2 : ZMod 2) = 0 by decide, zero_mul, add_zero,
      ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  · let _ : Fact p.Prime := ⟨hp⟩
    have hs : (-1 : ZMod p) ^ p = -1 := (hp.odd_of_ne_two h).neg_one_pow
    have hs₂ : (-1 : ZMod p) ^ (2 * p) = 1 := by
      rw [pow_mul]
      norm_num
    have hb := signedValue_second_difference p hn h
    simp only [a, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, pow_add, hs, hs₂, mul_one]
    linear_combination ((-1 : ZMod p) ^ n) * hb

