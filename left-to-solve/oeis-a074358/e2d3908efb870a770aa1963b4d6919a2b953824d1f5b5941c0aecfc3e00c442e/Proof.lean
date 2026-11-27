import OMAStatements.S_oeis_a074358

namespace A074358Proof

open OMA.S_oeis_a074358

private noncomputable def b (n : ℕ) : ℤ := (nu n).coeff 0

private theorem b_step (n : ℕ) : b (n + 2) = 2 * b (n + 1) + 2 * b n := by
  simp only [b, nu, Polynomial.coeff_add, Polynomial.mul_coeff_zero]
  have hg : (∑ i ∈ Finset.range (n + 1), (Polynomial.X : Polynomial ℤ)^i).coeff 0 = 1 := by
    simp [Polynomial.coeff_X_pow]
  rw [hg]
  norm_num

private theorem a_step (n : ℕ) : a (n + 3) = 2 * a (n + 2) + 2 * a (n + 1) + 2 * b (n + 1) := by
  change (2 * nu (n + 2) +
      2 * (∑ i ∈ Finset.range (n + 2), (Polynomial.X : Polynomial ℤ)^i) *
        nu (n + 1)).coeff 1 = _
  have range0 : (∑ i ∈ Finset.range (n + 2), (Polynomial.X : Polynomial ℤ)^i).coeff 0 = 1 := by
    simp [Polynomial.coeff_X_pow]
  have range1 : (∑ i ∈ Finset.range (n + 2), (Polynomial.X : Polynomial ℤ)^i).coeff 1 = 1 := by
    simp [Polynomial.coeff_X_pow, show 1 < n + 2 by omega]
  simp only [a, b, Polynomial.coeff_add, Polynomial.mul_coeff_one,
    Polynomial.mul_coeff_zero, range0, range1]
  norm_num
  ring

private theorem recurrence (n : ℕ) :
    a (n + 5) = 4 * a (n + 4) - 8 * a (n + 2) - 4 * a (n + 1) := by
  have h3 := a_step n
  have h4 := a_step (n + 1)
  have h5 := a_step (n + 2)
  have hb := b_step (n + 1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h4 h5 hb
  omega

private theorem initial : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 4 ∧ a 4 = 20 := by
  norm_num [a, nu, Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero,
    Finset.sum_range_succ, Polynomial.coeff_one]

open PowerSeries in
private theorem gf :
    (2 * X ^ 2 + 2 * X - 1 : ℤ⟦X⟧)^2 * mk a = 4 * X ^ 3 * (X + 1) := by
  have hden : (2 * X ^ 2 + 2 * X - 1 : ℤ⟦X⟧)^2 =
      1 - C 4 * X ^ 1 + C 8 * X ^ 3 + C 4 * X ^ 4 := by
    norm_num
    ring
  have hnum : (4 * X ^ 3 * (X + 1) : ℤ⟦X⟧) = C 4 * X ^ 3 + C 4 * X ^ 4 := by
    norm_num
    ring
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases hn : n < 5
  · obtain ⟨h0, h1, h2, h3, h4⟩ := initial
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [if_pos (show 1 ≤ k + 5 by omega), if_pos (show 3 ≤ k + 5 by omega),
    if_pos (show 4 ≤ k + 5 by omega)]
  simp only [if_neg (show k + 5 ≠ 3 by omega), if_neg (show k + 5 ≠ 4 by omega)]
  have h := recurrence k
  change a (k + 5) - 4 * a (k + 4) + 8 * a (k + 2) + 4 * a (k + 1) = 0 + 0
  omega

private theorem root_mode (r A B : ℝ) (hr : r^2 = 2*r + 2) (n : ℕ) :
    r^(n+4)*(A+B*(n+4)) =
      4*(r^(n+3)*(A+B*(n+3))) - 8*(r^(n+1)*(A+B*(n+1))) - 4*(r^n*(A+B*n)) := by
  have hr3 : r^3 = 6*r + 4 := by linear_combination (r+2)*hr
  have hr4 : r^4 = 16*r + 12 := by linear_combination r*hr3 + 6*hr
  simp only [pow_add, pow_one, hr4, hr3]
  ring

private theorem closed_eq (n : ℕ) :
    closed n = ((1 + Real.sqrt 3)^n * (-9 + 2*Real.sqrt 3 + 3*n) +
      (1 - Real.sqrt 3)^n * (-9 - 2*Real.sqrt 3 + 3*n)) / 18 := by
  unfold closed
  ring

private theorem closed_step (n : ℕ) :
    closed (n+4) = 4*closed (n+3) - 8*closed (n+1) - 4*closed n := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hp : (1 + Real.sqrt 3)^2 = 2*(1 + Real.sqrt 3) + 2 := by linear_combination hs
  have hm : (1 - Real.sqrt 3)^2 = 2*(1 - Real.sqrt 3) + 2 := by linear_combination hs
  have h := root_mode _ (-9+2*Real.sqrt 3) 3 hp n
  have h' := root_mode _ (-9-2*Real.sqrt 3) 3 hm n
  simp only [closed_eq, Nat.cast_add, Nat.cast_ofNat]
  linear_combination (h + h') / 18

set_option maxHeartbeats 1500000 in
private theorem closed_identifies (n : ℕ) (hn : 0 < n) : (a n : ℝ) = closed n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n < 5
    · obtain ⟨_, h1, h2, h3, h4⟩ := initial
      have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
      interval_cases n <;> norm_num [h1, h2, h3, h4, closed_eq]
      all_goals nlinarith only [hs, congrArg (fun x : ℝ => x * Real.sqrt 3) hs,
        congrArg (fun x : ℝ => x * (Real.sqrt 3)^2) hs]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    rw [recurrence k]
    push_cast
    rw [ih (k + 4) (by omega) (by omega), ih (k + 2) (by omega) (by omega),
      ih (k + 1) (by omega) (by omega)]
    exact (closed_step (k + 1)).symm

theorem solve : type_of% @main := by
  refine ⟨gf, closed_identifies, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  exact recurrence k

end A074358Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a074358.main :=
  A074358Proof.solve
