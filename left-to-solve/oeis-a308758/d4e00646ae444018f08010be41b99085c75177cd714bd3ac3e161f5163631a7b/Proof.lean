import OMAStatements.S_oeis_a308758
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.LinearCombination

namespace A308758Proof

open OMA.S_oeis_a308758 PowerSeries Finset

private theorem count_range (d n : ℕ) (hd : 0 < d) : (n+d)/d+1 = n/d+1+1 := by
  rw [Nat.add_div_right n hd]

private theorem accum_step (d : ℕ) (hd : 0 < d) (f : ℕ → ℤ) (n : ℕ) :
    accumulate d f (n+d) - accumulate d f n = f (n+d) := by
  have h (i : ℕ) : n+d-d*(i+1) = n-d*i := by simp [Nat.mul_add, Nat.add_sub_add_right]
  unfold accumulate
  rw [count_range d n hd, sum_range_succ']
  simp_rw [h]
  simp

private theorem weight_step (d : ℕ) (hd : 0 < d) (f : ℕ → ℤ) (n : ℕ) :
    weighted d f (n+d) - weighted d f n = accumulate d f n := by
  have h (i : ℕ) : n+d-d*(i+1) = n-d*i := by simp [Nat.mul_add, Nat.add_sub_add_right]
  unfold weighted accumulate
  rw [count_range d n hd, sum_range_succ']
  simp_rw [h]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero, add_mul, one_mul,
    sum_add_distrib]
  ring

private theorem geom (d : ℕ) (hd : 0 < d) (f : ℕ → ℤ) :
    (1-X^d)*mk (accumulate d f) = mk f := by
  ext n
  simp only [sub_mul, one_mul, map_sub, coeff_mk, coeff_X_pow_mul']
  by_cases hn : d ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n=k+d := ⟨n-d, by omega⟩
    simp only [if_pos (show d ≤ k+d by omega), Nat.add_sub_cancel]
    exact accum_step d hd f k
  · simp only [if_neg hn, sub_zero]
    have h : n/d=0 := Nat.div_eq_of_lt (by omega)
    simp [accumulate, h]

private theorem weighted_geom (d : ℕ) (hd : 0 < d) (f : ℕ → ℤ) :
    (1-X^d)*mk (weighted d f) = X^d*mk (accumulate d f) := by
  ext n
  simp only [sub_mul, one_mul, map_sub, coeff_mk, coeff_X_pow_mul']
  by_cases hn : d ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n=k+d := ⟨n-d, by omega⟩
    simp only [if_pos (show d ≤ k+d by omega), Nat.add_sub_cancel]
    exact weight_step d hd f k
  · simp only [if_neg hn, sub_zero]
    have h : n/d=0 := Nat.div_eq_of_lt (by omega)
    simp [weighted, h]

private theorem ones_gf : (1-X)*mk ones = 1 := by
  ext n
  cases n <;> simp [sub_mul, coeff_succ_X_mul, ones]

private theorem shifted : mk a = X^4*(mk partCount+mk pWeight+mk qWeight) := by
  ext n
  simp only [coeff_mk, coeff_X_pow_mul', a, map_add]

private theorem gf :
    ((1-X)^5*(1+X)^3*(1+X^2)^2*(1+X+X^2)^2 : ℤ⟦X⟧)*mk a =
      X^4*(1+X+X^2+X^3+X^4+X^5+X^6) := by
  have hc4 : (1-X^4)*mk partCount = mk triples := geom 4 (by decide) triples
  have hc3 : (1-X^3)*mk triples = mk pairs := geom 3 (by decide) pairs
  have hc2 : (1-X^2)*mk pairs = mk ones := geom 2 (by decide) ones
  have hp4 : (1-X^4)*mk pWeight = X^4*mk partCount := weighted_geom 4 (by decide) triples
  have hq4 : (1-X^4)*mk qWeight = mk (weighted 3 pairs) := geom 4 (by decide) _
  have hq3 : (1-X^3)*mk (weighted 3 pairs) = X^3*mk triples := weighted_geom 3 (by decide) pairs
  have ht : (1-X)*(1-X^2)*(1-X^3)*mk triples = 1 := by
    rw [mul_assoc ((1-X)*(1-X^2)), hc3]
    rw [mul_assoc, hc2, ones_gf]
  have hc : (1-X)*(1-X^2)*(1-X^3)*(1-X^4)*mk partCount = 1 := by
    rw [mul_assoc ((1-X)*(1-X^2)*(1-X^3)), hc4]
    exact ht
  have hq : (1-X^3)*(1-X^4)*mk qWeight = X^3*mk triples := by
    rw [mul_assoc, hq4, hq3]
  have hne : (1-X : ℤ⟦X⟧) ≠ 0 := by
    intro h
    have h0 := congrArg (coeff 0) h
    norm_num [map_sub, coeff_X] at h0
  apply mul_left_cancel₀ hne
  rw [shifted, ← mul_assoc]
  have hd : (1-X)*((1-X)^5*(1+X)^3*(1+X^2)^2*(1+X+X^2)^2 : ℤ⟦X⟧) =
      (1-X)*(1-X^2)*(1-X^3)^2*(1-X^4)^2 := by ring
  rw [hd]
  have hC : (1-X)*(1-X^2)*(1-X^3)^2*(1-X^4)^2*mk partCount =
      (1-X^3)*(1-X^4) := by
    linear_combination ((1-X^3)*(1-X^4))*hc
  have hP : (1-X)*(1-X^2)*(1-X^3)^2*(1-X^4)^2*mk pWeight =
      (1-X^3)*X^4 := by
    linear_combination ((1-X)*(1-X^2)*(1-X^3)^2*(1-X^4))*hp4 + ((1-X^3)*X^4)*hc
  have hQ : (1-X)*(1-X^2)*(1-X^3)^2*(1-X^4)^2*mk qWeight =
      (1-X^4)*X^3 := by
    linear_combination ((1-X)*(1-X^2)*(1-X^3)*(1-X^4))* hq + ((1-X^4)*X^3)*ht
  linear_combination X^4*hC + X^4*hP + X^4*hQ

private theorem recurrence (n : ℕ) (hn : 15 < n) :
    a n = a (n-2) + 2*a (n-3) + 2*a (n-4) - 2*a (n-5) - 3*a (n-6) - 4*a (n-7)
      + 4*a (n-9) + 3*a (n-10) + 2*a (n-11) - 2*a (n-12) - 2*a (n-13)
      - a (n-14) + a (n-16) := by
  have hd : ((1-X)^5*(1+X)^3*(1+X^2)^2*(1+X+X^2)^2 : ℤ⟦X⟧) =
      1-X^2-C 2*X^3-C 2*X^4+C 2*X^5+C 3*X^6+C 4*X^7-C 4*X^9-C 3*X^10
        -C 2*X^11+C 2*X^12+C 2*X^13+X^14-X^16 := by norm_num; ring
  have hp : (X^4*(1+X+X^2+X^3+X^4+X^5+X^6) : ℤ⟦X⟧) =
      X^4+X^5+X^6+X^7+X^8+X^9+X^10 := by ring
  have h := gf
  rw [hd,hp] at h
  have h := congrArg (coeff n) h
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow,
    if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega),
    if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega), if_pos (show 7 ≤ n by omega),
    if_pos (show 9 ≤ n by omega), if_pos (show 10 ≤ n by omega), if_pos (show 11 ≤ n by omega),
    if_pos (show 12 ≤ n by omega), if_pos (show 13 ≤ n by omega), if_pos (show 14 ≤ n by omega),
    if_pos (show 16 ≤ n by omega), if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega),
    if_neg (show n ≠ 6 by omega), if_neg (show n ≠ 7 by omega), if_neg (show n ≠ 8 by omega),
    if_neg (show n ≠ 9 by omega), if_neg (show n ≠ 10 by omega)] at h
  omega

end A308758Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a308758.main :=
  ⟨A308758Proof.gf, A308758Proof.recurrence⟩
