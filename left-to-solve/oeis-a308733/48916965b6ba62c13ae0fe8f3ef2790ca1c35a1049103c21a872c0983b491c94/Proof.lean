import OMAStatements.S_oeis_a308733
import Mathlib.Tactic.Ring

namespace A308733Proof

open OMA.S_oeis_a308733 PowerSeries Finset

private def count (m : ℕ) : ℤ :=
  ∑ p ∈ range (m / 4 + 1), triples (m-4*p)

private theorem triples_first (m : ℕ) (hm : m < 3) : triples m = pairs m := by
  have h : m/3 = 0 := Nat.div_eq_of_lt hm
  simp [triples, h]

private theorem count_first (m : ℕ) (hm : m < 4) : count m = triples m := by
  have h : m/4 = 0 := Nat.div_eq_of_lt hm
  simp [count, h]

private theorem weight_first (m : ℕ) (hm : m < 4) : weight m = count m := by
  have h : m/4 = 0 := Nat.div_eq_of_lt hm
  simp [weight, count, h]

private theorem pairs_step (m : ℕ) : pairs (m+2) - pairs m = 1 := by
  have h : (m+2)/2 = m/2+1 := by omega
  simp only [pairs, h, Nat.cast_add, Nat.cast_one]
  ring

private theorem triples_step (m : ℕ) : triples (m+3) - triples m = pairs (m+3) := by
  have hc : (m+3)/3 + 1 = m/3+1+1 := by omega
  have hi (i : ℕ) : (m+3)-3*(i+1) = m-3*i := by omega
  unfold triples
  rw [hc, sum_range_succ']
  simp_rw [hi]
  simp

private theorem count_step (m : ℕ) : count (m+4) - count m = triples (m+4) := by
  have hc : (m+4)/4 + 1 = m/4+1+1 := by omega
  have hi (i : ℕ) : (m+4)-4*(i+1) = m-4*i := by omega
  unfold count
  rw [hc, sum_range_succ']
  simp_rw [hi]
  simp

private theorem weight_step (m : ℕ) : weight (m+4) - weight m = count (m+4) := by
  have hc : (m+4)/4 + 1 = m/4+1+1 := by omega
  have hi (i : ℕ) : (m+4)-4*(i+1) = m-4*i := by omega
  have hsum :
      weight (m+4) =
      (∑ i ∈ range (m/4+1), (((i : ℤ)+1)*triples (m-4*i) + triples (m-4*i))) +
        triples (m+4) := by
    unfold weight
    rw [hc, sum_range_succ']
    simp_rw [hi]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, one_mul, mul_zero,
      Nat.sub_zero]
    rw [add_left_inj]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hsum, sum_add_distrib]
  change weight m + count m + triples (m+4) - weight m = count (m+4)
  have h := count_step m
  omega

private theorem step_series (r : ℕ) (f g : ℕ → ℤ)
    (base : ∀ n < r, f n = g n) (step : ∀ n, f (n+r) - f n = g (n+r)) :
    (1-X^r)*mk f = mk g := by
  ext n
  simp only [sub_mul, one_mul, map_sub, coeff_mk, coeff_X_pow_mul']
  by_cases h : r ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+r := ⟨n-r, by omega⟩
    simp only [if_pos (show r ≤ k+r by omega), Nat.add_sub_cancel]
    exact step k
  · simp only [if_neg h, sub_zero]
    exact base n (by omega)

private theorem ones :
    (1-X) * mk (fun _ : ℕ ↦ (1 : ℤ)) = 1 := by
  ext n
  cases n <;> simp [sub_mul, coeff_succ_X_mul]

private theorem shifted : mk a = X^4 * mk weight := by
  ext n
  simp only [coeff_mk, coeff_X_pow_mul', a]

private theorem gf :
    ((1-X)^5*(1+X)^3*(1+X^2)^2*(1+X+X^2) : ℤ⟦X⟧) * mk a = X^4 := by
  have hweight := step_series 4 weight count weight_first weight_step
  have hcount := step_series 4 count triples count_first count_step
  have htriples := step_series 3 triples pairs triples_first triples_step
  have hpairs := step_series 2 pairs (fun _ ↦ 1) (by
    intro m hm
    have h : m/2 = 0 := Nat.div_eq_of_lt hm
    simp [pairs, h]) pairs_step
  calc
    _ = X^4 * ((1-X) * ((1-X^2) * ((1-X^3) * ((1-X^4) * ((1-X^4)*mk weight))))) := by
      rw [shifted]
      ring
    _ = X^4 := by rw [hweight, hcount, htriples, hpairs, ones, mul_one]

private theorem recurrence (n : ℕ) (hn : 13 < n) :
    a n = a (n-1) + a (n-2) + a (n-4) - 3*a (n-5) - a (n-6) + a (n-8)
      + 3*a (n-9) - a (n-10) - a (n-12) - a (n-13) + a (n-14) := by
  have hd : ((1-X)^5*(1+X)^3*(1+X^2)^2*(1+X+X^2) : ℤ⟦X⟧) =
      1-X^1-X^2-X^4+C 3*X^5+X^6-X^8-C 3*X^9+X^10+X^12+X^13-X^14 := by
    norm_num
    ring
  have h := gf
  rw [hd] at h
  have h := congrArg (coeff n) h
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow,
    if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
    if_pos (show 4 ≤ n by omega), if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega),
    if_pos (show 8 ≤ n by omega), if_pos (show 9 ≤ n by omega), if_pos (show 10 ≤ n by omega),
    if_pos (show 12 ≤ n by omega), if_pos (show 13 ≤ n by omega), if_pos (show 14 ≤ n by omega),
    if_neg (show n ≠ 4 by omega)] at h
  omega

end A308733Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a308733.main :=
  ⟨A308733Proof.gf, A308733Proof.recurrence⟩
