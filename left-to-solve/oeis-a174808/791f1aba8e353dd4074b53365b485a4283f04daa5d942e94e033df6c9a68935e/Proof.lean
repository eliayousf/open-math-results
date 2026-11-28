import OMAStatements.S_oeis_a174808

/-!
Paul Barry introduced A174808 and R. J. Mathar conjectured the recurrence.
The coefficient transform in the OEIS entry is substitution by X + X².
Source: https://oeis.org/A174808
-/

namespace A174808Proof

open OMA.S_oeis_a174808 PowerSeries

private noncomputable def u : ℤ⟦X⟧ := X + X ^ 2

private theorem hu : HasSubst u := by
  exact HasSubst.of_constantCoeff_zero' (by simp [u])

private noncomputable def F : ℤ⟦X⟧ :=
  (PowerSeries.map (Nat.castRingHom ℤ) largeSchroderSeries).subst u

private theorem coeff_u_pow (n k : ℕ) :
    coeff n (u ^ k) = if k ≤ n then (k.choose (n - k) : ℤ) else 0 := by
  have h : u ^ k = X ^ k * (1 + X) ^ k := by
    rw [show u = X * (1 + X) by unfold u; ring, mul_pow]
  rw [h, coeff_X_pow_mul']
  split_ifs
  · have hc : (1 + X : ℤ⟦X⟧) ^ k =
        (((1 + Polynomial.X : Polynomial ℤ) ^ k : Polynomial ℤ) : ℤ⟦X⟧) := by
      simp
    rw [hc, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  · rfl

private theorem coeff_F (n : ℕ) : coeff n F = a n := by
  classical
  unfold F
  rw [coeff_subst' hu, finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · unfold a
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
    simp [coeff_map, coeff_u_pow, hkn, mul_comm]
  · intro k hk
    by_contra h
    have hn : ¬ k ≤ n := by simpa [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff] using h
    apply hk
    simp [coeff_u_pow, hn]

private theorem quadratic : F = 1 + u * F + u * F ^ 2 := by
  let r := PowerSeries.map (Nat.castRingHom ℤ)
  have h_one : (1 : ℤ⟦X⟧).subst u = 1 := by
    rw [← coe_substAlgHom hu, map_one]
  have hs := congrArg (fun f : ℕ⟦X⟧ => substAlgHom hu (r f))
    largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
  simpa [r, F, coe_substAlgHom, subst_add hu, subst_mul hu, subst_pow hu, subst_X hu,
    h_one] using hs

private theorem differential :
    (1 - 5 * X - 11 * X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4 + X ^ 5) *
      (X * derivative ℤ F) + (1 - X - 9 * X ^ 2 - 6 * X ^ 3) * F =
      1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 := by
  let S : ℤ⟦X⟧ := 1 - u - 2 * u * F
  let D : ℤ⟦X⟧ := 1 - 6 * u + u ^ 2
  have hS : S ^ 2 = D := by
    dsimp [S, D]
    linear_combination -4 * u * quadratic
  have hDS : 2 * S * derivative ℤ S = derivative ℤ D := by
    have h := congrArg (derivative ℤ) hS
    simpa [derivative_pow, mul_assoc] using h
  have hd : 2 * D * derivative ℤ S = S * derivative ℤ D := calc
    2 * D * derivative ℤ S = S * (2 * S * derivative ℤ S) := by rw [← hS]; ring
    _ = _ := by rw [hDS]
  have d₂ : derivative ℤ (2 : ℤ⟦X⟧) = 0 := (derivative ℤ).map_natCast 2
  have d₆ : derivative ℤ (6 : ℤ⟦X⟧) = 0 := (derivative ℤ).map_natCast 6
  have du : derivative ℤ u = 1 + 2 * X := by
    simp [u, mul_comm]
  have hdS : derivative ℤ S =
      -(1 + 2 * X) - 2 * (1 + 2 * X) * F - 2 * u * derivative ℤ F := by
    simp [S, Derivation.leibniz, smul_eq_mul, d₂, du]
    ring
  have hdD : derivative ℤ D = (2 * u - 6) * (1 + 2 * X) := by
    simp [D, Derivation.leibniz, smul_eq_mul, d₆, du]
    ring
  have h₄ : (4 : ℤ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (constantCoeff (R := ℤ)) h
    change constantCoeff ((4 : ℕ) : ℤ⟦X⟧) = 0 at h'
    rw [map_natCast] at h'
    norm_num at h'
  apply mul_left_cancel₀ (a := (4 : ℤ⟦X⟧)) h₄
  rw [hdS, hdD] at hd
  dsimp [S, D, u] at hd
  linear_combination -hd

private theorem euler_coeff (n : ℕ) :
    coeff n (X * derivative ℤ F) = (n : ℤ) * a n := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_succ_X_mul, coeff_derivative, coeff_F, mul_comm]

end A174808Proof

open OMA.S_oeis_a174808 PowerSeries A174808Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a174808.main := by
  intro n hn
  let E : ℤ⟦X⟧ := X * derivative ℤ F
  have hC (k : ℕ) : C (k : ℤ) = (k : ℤ⟦X⟧) := map_natCast C k
  have hC₂ : C (2 : ℤ) = (2 : ℤ⟦X⟧) := hC 2
  have hC₃ : C (3 : ℤ) = (3 : ℤ⟦X⟧) := hC 3
  have hC₅ : C (5 : ℤ) = (5 : ℤ⟦X⟧) := hC 5
  have hC₆ : C (6 : ℤ) = (6 : ℤ⟦X⟧) := hC 6
  have hC₉ : C (9 : ℤ) = (9 : ℤ⟦X⟧) := hC 9
  have hC₁₁ : C (11 : ℤ) = (11 : ℤ⟦X⟧) := hC 11
  have h : E - C 5 * (X * E) - C 11 * (X ^ 2 * E) - C 3 * (X ^ 3 * E) +
      C 3 * (X ^ 4 * E) + X ^ 5 * E + (F - X * F - C 9 * (X ^ 2 * F) - C 6 * (X ^ 3 * F)) =
      1 + C 3 * X + C 3 * X ^ 2 + C 2 * X ^ 3 := by
    rw [hC₂, hC₃, hC₅, hC₆, hC₉, hC₁₁]
    linear_combination differential
  have hₙ := congrArg (coeff n) h
  have h₁ : 1 ≤ n := by omega
  have h₂ : 2 ≤ n := by omega
  have h₃ : 3 ≤ n := by omega
  have h₄ : 4 ≤ n := by omega
  have hn₀ : n ≠ 0 := by omega
  have hn₁ : n ≠ 1 := by omega
  have hn₂ : n ≠ 2 := by omega
  have hn₃ : n ≠ 3 := by omega
  have hshift (f : ℤ⟦X⟧) : coeff n (X * f) = coeff (n - 1) f := by
    simpa using (coeff_X_pow_mul' f 1 n).trans (if_pos h₁)
  simp only [map_add, map_sub, coeff_C_mul, hshift, coeff_X_pow_mul',
    if_pos h₂, if_pos h₃, if_pos h₄, if_pos hn, coeff_X, coeff_one, coeff_X_pow,
    if_neg hn₀, if_neg hn₁, if_neg hn₂, if_neg hn₃, mul_zero, add_zero] at hₙ
  simp only [E, euler_coeff, coeff_F] at hₙ
  rw [Nat.cast_sub h₁, Nat.cast_sub h₂, Nat.cast_sub h₃, Nat.cast_sub h₄, Nat.cast_sub hn] at hₙ
  linear_combination hₙ
