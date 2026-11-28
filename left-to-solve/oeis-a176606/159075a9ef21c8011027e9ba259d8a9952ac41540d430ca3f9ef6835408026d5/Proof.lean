import OMAStatements.S_oeis_a176606

/-!
Richard Choulet defined A176606, and R. J. Mathar conjectured the linear recurrence.
The proof derives a differential equation from the quadratic generating function.
Source: https://oeis.org/A176606
-/

namespace A176606Proof

open OMA.S_oeis_a176606 PowerSeries

private theorem prefix_length (n : ℕ) : (aList n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp [aList, ih]

private theorem prefix_value (n k : ℕ) (hk : k ≤ n) : (aList n).getD k 0 = a k := by
  induction n with
  | zero =>
    have : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    rcases eq_or_lt_of_le hk with rfl | h
    · rfl
    cases n with
    | zero =>
      have : k = 0 := by omega
      subst k
      rfl
    | succ n =>
      rw [aList, List.getD_append]
      · exact ih (by omega)
      · rw [prefix_length]
        omega

private theorem convolution (n : ℕ) :
    a (n + 2) = (∑ k ∈ Finset.range (n + 2), a k * a (n + 1 - k)) + 1 := by
  unfold a at ⊢
  rw [aList, List.getD_append_right _ _ _ _ (by rw [prefix_length])]
  rw [prefix_length]
  simp only [Nat.sub_self]
  change _ + 1 = _ + 1
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  change (aList (n + 1)).getD k 0 * (aList (n + 1)).getD (n + 1 - k) 0 =
    a k * a (n + 1 - k)
  rw [prefix_value _ _ (by omega), prefix_value _ _ (by omega)]

private noncomputable def series : ℚ⟦X⟧ := mk fun n => (a n : ℚ)

private theorem quadratic :
    (1 - X) * (series - X * series ^ 2) = 1 + X - X ^ 2 := by
  let F := series - X * series ^ 2
  have hF (n : ℕ) : coeff (n + 2) F = 1 := by
    change coeff (n + 1).succ (series - X * series ^ 2) = 1
    rw [map_sub, coeff_succ_X_mul]
    simp only [series, coeff_mk, pow_two, coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (a i : ℚ) * a j)]
    have h := congrArg (fun z : ℤ => (z : ℚ)) (convolution n)
    push_cast at h
    linarith
  have hF₀ : coeff 0 F = 1 := by
    simp [F, series, a, aList]
  have hF₁ : coeff 1 F = 2 := by
    change coeff (Nat.succ 0) (series - X * series ^ 2) = 2
    rw [map_sub, coeff_succ_X_mul]
    norm_num [series, a, aList]
  change (1 - X) * F = _
  rw [sub_mul, one_mul]
  ext n
  rcases n with _ | _ | _ | n
  · norm_num [coeff_X, coeff_X_pow]
    exact (coeff_zero_eq_constantCoeff_apply F) ▸ hF₀
  · norm_num [hF₀, hF₁, coeff_X, coeff_X_pow, coeff_succ_X_mul]
  · norm_num [hF₁, hF 0, coeff_X, coeff_X_pow, coeff_succ_X_mul]
  · have hn₂ : n + 3 ≠ 2 := by omega
    change coeff (n + 3) (F - X * F) = _
    simp [hF (n + 1), hF n, hn₂, coeff_one, coeff_X, coeff_X_pow]

private theorem differential :
    (1 - 6 * X + X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4) * (X * derivative ℚ series) +
      (1 - 4 * X + 5 * X ^ 2) * series = 1 + 2 * X - 4 * X ^ 2 + 2 * X ^ 3 := by
  let S : ℚ⟦X⟧ := (1 - X) * (1 - 2 * X * series)
  let P : ℚ⟦X⟧ := 1 - 6 * X + X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4
  let Q : ℚ⟦X⟧ := 1 - 5 * X - 4 * X ^ 2 + 4 * X ^ 3
  have hS : S ^ 2 = P := calc
    S ^ 2 = (1 - X) ^ 2 - 4 * X * (1 - X) * ((1 - X) * (series - X * series ^ 2)) := by
      dsimp [S]
      ring
    _ = P := by rw [quadratic]; dsimp [P]; ring
  have hP : P = (1 - X) * Q := by dsimp [P, Q]; ring
  have dh : 2 * S * derivative ℚ S = derivative ℚ P := by
    have h := congrArg (derivative ℚ) hS
    simpa [derivative_pow, mul_assoc] using h
  have hd : 2 * P * derivative ℚ S = S * derivative ℚ P := calc
    2 * P * derivative ℚ S = S * (2 * S * derivative ℚ S) := by rw [← hS]; ring
    _ = _ := by rw [dh]
  have dNat (k : ℕ) : derivative ℚ (k : ℚ⟦X⟧) = 0 := (derivative ℚ).map_natCast k
  have d₂ : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dNat 2
  have d₄ : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dNat 4
  have d₆ : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dNat 6
  have d₈ : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dNat 8
  have hdS : derivative ℚ S = -1 + (4 * X - 2) * series -
      2 * X * (1 - X) * derivative ℚ series := by
    simp [S, Derivation.leibniz, smul_eq_mul, d₂]
    ring
  have hdP : derivative ℚ P = -6 + 2 * X + 24 * X ^ 2 - 16 * X ^ 3 := by
    simp [P, Derivation.leibniz, smul_eq_mul, d₄, d₆, d₈]
    ring
  have hx : (1 - X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h₀ := congrArg (coeff 0) h
    simp at h₀
  have h₄ : (4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (constantCoeff (R := ℚ)) h
    change constantCoeff ((4 : ℕ) : ℚ⟦X⟧) = 0 at h'
    rw [map_natCast] at h'
    norm_num at h'
  apply mul_left_cancel₀ (a := (4 : ℚ⟦X⟧) * (1 - X)) (mul_ne_zero h₄ hx)
  rw [hdS, hdP] at hd
  dsimp [S] at hd
  rw [hP] at hd
  dsimp [Q] at hd
  linear_combination -hd

private theorem euler_coeff (n : ℕ) :
    coeff n (X * derivative ℚ series) = (n : ℚ) * a n := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_succ_X_mul, coeff_derivative, series, mul_comm]

theorem recurrence : type_of% @OMA.S_oeis_a176606.main := by
  intro n hn
  let E : ℚ⟦X⟧ := X * derivative ℚ series
  have hC (k : ℕ) : C (k : ℚ) = (k : ℚ⟦X⟧) := map_natCast C k
  have hC₂ : C (2 : ℚ) = (2 : ℚ⟦X⟧) := hC 2
  have hC₄ : C (4 : ℚ) = (4 : ℚ⟦X⟧) := hC 4
  have hC₅ : C (5 : ℚ) = (5 : ℚ⟦X⟧) := hC 5
  have hC₆ : C (6 : ℚ) = (6 : ℚ⟦X⟧) := hC 6
  have hC₈ : C (8 : ℚ) = (8 : ℚ⟦X⟧) := hC 8
  have h : E - C 6 * (X * E) + X ^ 2 * E + C 8 * (X ^ 3 * E) - C 4 * (X ^ 4 * E) +
      (series - C 4 * (X * series) + C 5 * (X ^ 2 * series)) =
      1 + C 2 * X - C 4 * X ^ 2 + C 2 * X ^ 3 := by
    calc
      _ = (1 - 6 * X + X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4) * E +
          (1 - 4 * X + 5 * X ^ 2) * series := by rw [hC₆, hC₈, hC₄, hC₅]; ring
      _ = _ := by rw [hC₂, hC₄]; exact differential
  have hₙ := congrArg (coeff n) h
  have h₁ : 1 ≤ n := by omega
  have h₂ : 2 ≤ n := by omega
  have h₃ : 3 ≤ n := by omega
  have hn₀ : n ≠ 0 := by omega
  have hn₁ : n ≠ 1 := by omega
  have hn₂ : n ≠ 2 := by omega
  have hn₃ : n ≠ 3 := by omega
  have hshift (f : ℚ⟦X⟧) : coeff n (X * f) = coeff (n - 1) f := by
    simpa using (coeff_X_pow_mul' f 1 n).trans (if_pos h₁)
  simp only [map_add, map_sub, coeff_C_mul, hshift,
    coeff_X_pow_mul', if_pos h₂, if_pos h₃, if_pos hn, coeff_X,
    coeff_one, coeff_X_pow, if_neg hn₀, if_neg hn₁, if_neg hn₂, if_neg hn₃,
    mul_zero, add_zero, sub_zero] at hₙ
  simp only [E, euler_coeff] at hₙ
  simp only [series, coeff_mk] at hₙ
  rw [Nat.cast_sub h₁, Nat.cast_sub h₂, Nat.cast_sub h₃, Nat.cast_sub hn] at hₙ
  have hq : ((n : ℚ) + 1) * a n + 2 * (-3 * (n : ℚ) + 1) * a (n - 1) +
      ((n : ℚ) + 3) * a (n - 2) + 8 * ((n : ℚ) - 3) * a (n - 3) +
      4 * (-(n : ℚ) + 4) * a (n - 4) = 0 := by
    linear_combination hₙ
  exact_mod_cast hq

end A176606Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a176606.main := A176606Proof.recurrence
