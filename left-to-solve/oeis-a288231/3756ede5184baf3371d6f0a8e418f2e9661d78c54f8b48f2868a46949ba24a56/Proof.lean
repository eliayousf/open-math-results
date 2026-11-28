import OMAStatements.S_oeis_a288231
import Mathlib

/-!
Clark Kimberling conjectured the strict increase of A288231.
The proof establishes that consecutive terms grow by a factor of at least 3/2.
Source: https://oeis.org/A288231
The coefficient argument also appears in the companion submission for A288230.
-/

namespace A288231Proof

open OMA.S_oeis_a288231 PowerSeries

private noncomputable def r : ℝ := (4 : ℝ) ^ (1 / 3 : ℝ)
private noncomputable def D : ℚ⟦X⟧ := denominator r
private noncomputable def d (n : ℕ) : ℚ := (-1) ^ n * weight r n
private noncomputable def E : ℚ⟦X⟧ := (1 + X) ^ 2 * D
private noncomputable def e (n : ℕ) : ℚ := coeff n E

private theorem parameter_bounds : 3 / 2 ≤ r ∧ r < 8 / 5 := by
  have hr : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hc : r ^ 3 = 4 := by
    calc
      r ^ 3 = (4 : ℝ) ^ ((1 / 3 : ℝ) * ((3 : ℕ) : ℝ)) :=
        (Real.rpow_mul_natCast (by norm_num) _ 3).symm
      _ = 4 := by norm_num
  constructor
  · apply le_of_pow_le_pow_left₀ (n := 3) (by decide) hr
    rw [hc]
    norm_num
  · apply lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0 : ℝ) ≤ 8 / 5)
    rw [hc]
    norm_num

private theorem floor_value (n : ℕ) (m : ℤ)
    (hl : (m : ℝ) ≤ ((n : ℝ) + 1) * (3 / 2))
    (hu : ((n : ℝ) + 1) * (8 / 5) ≤ (m : ℝ) + 1) :
    weight r n = (m : ℚ) := by
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  have h : ⌊((n : ℝ) + 1) * r⌋ = m := Int.floor_eq_iff.mpr
    ⟨hl.trans (mul_le_mul_of_nonneg_left parameter_bounds.1 hpos.le),
      (mul_lt_mul_of_pos_left parameter_bounds.2 hpos).trans_le hu⟩
  rw [weight, h]

private theorem floor_step (n : ℕ) :
    1 ≤ weight r (n + 1) - weight r n ∧ weight r (n + 1) - weight r n ≤ 2 := by
  let y := ((n : ℝ) + 1) * r
  have hl : y + 1 ≤ (((n + 1 : ℕ) : ℝ) + 1) * r := by
    dsimp [y]
    push_cast
    linarith [parameter_bounds.1]
  have hu : (((n + 1 : ℕ) : ℝ) + 1) * r ≤ y + (2 : ℤ) := by
    dsimp [y]
    push_cast
    linarith [parameter_bounds.2]
  have hL := Int.floor_mono hl
  have hU := Int.floor_mono hu
  rw [Int.floor_add_one] at hL
  rw [Int.floor_add_intCast] at hU
  have hL' : 1 ≤ ⌊(((n + 1 : ℕ) : ℝ) + 1) * r⌋ - ⌊y⌋ := by omega
  have hU' : ⌊(((n + 1 : ℕ) : ℝ) + 1) * r⌋ - ⌊y⌋ ≤ 2 := by omega
  dsimp [y] at hL' hU'
  constructor <;> unfold weight
  · exact_mod_cast hL'
  · exact_mod_cast hU'

private theorem expand_E : E = D + C 2 * (X * D) + X ^ 2 * D := by
  have htwo : C (2 : ℚ) = (2 : ℚ⟦X⟧) := map_natCast C 2
  rw [htwo]
  unfold E
  ring

private theorem coeff_D (n : ℕ) : coeff n D = d n := by
  simp [D, denominator, d]

private theorem e_zero : e 0 = d 0 := by
  change coeff 0 E = d 0
  rw [expand_E, map_add, map_add, coeff_C_mul, coeff_zero_X_mul, coeff_X_pow_mul',
    if_neg (by decide : ¬ 2 ≤ 0), mul_zero, add_zero, add_zero, coeff_D]

private theorem e_one : e 1 = d 1 + 2 * d 0 := by
  simp [e, expand_E, coeff_D, coeff_X_pow_mul']

private theorem e_later (n : ℕ) : e (n + 2) = d (n + 2) + 2 * d (n + 1) + d n := by
  change coeff ((n + 1) + 1) E = _
  rw [expand_E, map_add, map_add, coeff_C_mul, coeff_succ_X_mul]
  rw [show n + 1 + 1 = n + 2 by omega, coeff_X_pow_mul D 2 n]
  simp only [coeff_D]

private theorem e_bound (n : ℕ) : |e (n + 2)| ≤ 1 := by
  rw [e_later]
  have h :
      d (n + 2) + 2 * d (n + 1) + d n =
        (-1) ^ n * (weight r (n + 2) - 2 * weight r (n + 1) + weight r n) := by
    simp only [d, pow_add]
    ring
  rw [h, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  apply abs_le.mpr
  have h₀ := floor_step n
  have h₁ := floor_step (n + 1)
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2]

private theorem e_initial :
    e 0 = 1 ∧ e 1 = -1 ∧ e 2 = -1 ∧ e 3 = -1 ∧ e 4 = -1 ∧ e 5 = -1 := by
  have w₀ : weight r 0 = 1 := by norm_num [floor_value 0 1 (by norm_num) (by norm_num)]
  have w₁ : weight r 1 = 3 := by norm_num [floor_value 1 3 (by norm_num) (by norm_num)]
  have w₂ : weight r 2 = 4 := by norm_num [floor_value 2 4 (by norm_num) (by norm_num)]
  have w₃ : weight r 3 = 6 := by norm_num [floor_value 3 6 (by norm_num) (by norm_num)]
  have w₄ : weight r 4 = 7 := by norm_num [floor_value 4 7 (by norm_num) (by norm_num)]
  have w₅ : weight r 5 = 9 := by norm_num [floor_value 5 9 (by norm_num) (by norm_num)]
  norm_num [e_zero, e_one, e_later 0, e_later 1, e_later 2, e_later 3, d,
    w₀, w₁, w₂, w₃, w₄, w₅]

private noncomputable def h : ℕ → ℚ
  | 0 => 1
  | n + 1 => (3 / 2) * h n + e (n + 1) - e n / 2

private theorem h_initial :
    h 1 = 0 ∧ h 2 = -1/2 ∧ h 3 = -5/4 ∧ h 4 = -19/8 ∧ h 5 = -65/16 := by
  rcases e_initial with ⟨e₀, e₁, e₂, e₃, e₄, e₅⟩
  norm_num [h, e₀, e₁, e₂, e₃, e₄, e₅]

private theorem h_later (n : ℕ) : h (n + 5) ≤ -3 := by
  induction n with
  | zero => rw [show 0 + 5 = 5 by decide, h_initial.2.2.2.2]; norm_num
  | succ n ih =>
    change (3 / 2) * h (n + 5) + e (n + 5 + 1) - e (n + 5) / 2 ≤ -3
    have hl := (abs_le.mp (e_bound (n + 3))).1
    have hu := (abs_le.mp (e_bound (n + 4))).2
    linarith

private theorem h_nonpos (n : ℕ) (hn : 0 < n) : h n ≤ 0 := by
  by_cases ht : 5 ≤ n
  · have he : n - 5 + 5 = n := Nat.sub_add_cancel ht
    have hh := h_later (n - 5)
    rw [he] at hh
    linarith
  · rcases h_initial with ⟨h₁, h₂, h₃, h₄, _⟩
    interval_cases n <;> norm_num [h₁, h₂, h₃, h₄]

private noncomputable def H : ℚ⟦X⟧ := mk h
private noncomputable def I : ℚ⟦X⟧ := 1 - C (3 / 2) * X
private noncomputable def J : ℚ⟦X⟧ := 1 - C (1 / 2) * X
private noncomputable def B : ℚ⟦X⟧ := I * D⁻¹
private noncomputable def b (n : ℕ) : ℚ := coeff n B

private theorem linear_coeff (c : ℚ) (F : ℚ⟦X⟧) (n : ℕ) :
    coeff (n + 1) ((1 - C c * X) * F) = coeff (n + 1) F - c * coeff n F := by
  rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_succ_X_mul]

private theorem modified_denominator : I * H = J * E := by
  ext n
  cases n with
  | zero =>
    change coeff 0 ((1 - C (3 / 2) * X) * H) = coeff 0 ((1 - C (1 / 2) * X) * E)
    simp only [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_zero_X_mul,
      mul_zero, sub_zero, H, coeff_mk]
    exact e_initial.1.symm
  | succ n =>
    change coeff (n + 1) ((1 - C (3 / 2) * X) * H) =
      coeff (n + 1) ((1 - C (1 / 2) * X) * E)
    rw [linear_coeff, linear_coeff]
    simp only [H, coeff_mk, h, e]
    ring

private theorem denominator_constant : constantCoeff D = 1 := by
  have hd := e_initial.1
  rw [e_zero, ← coeff_D, coeff_zero_eq_constantCoeff_apply] at hd
  exact hd

private theorem product : H * B = 1 + C (3 / 2) * X - C (1 / 2) * X ^ 3 := calc
  H * B = (I * H) * D⁻¹ := by unfold B; ring
  _ = J * (1 + X) ^ 2 * (D * D⁻¹) := by rw [modified_denominator]; unfold E; ring
  _ = _ := by
    rw [PowerSeries.mul_inv_cancel _ (by rw [denominator_constant]; norm_num), mul_one]
    have hhalf : C (1 / 2 : ℚ) + C (1 / 2 : ℚ) = 1 := by
      rw [← map_add]
      norm_num
    have hratio : C (3 / 2 : ℚ) = 1 + C (1 / 2 : ℚ) := by
      rw [← C.map_one, ← map_add]
      norm_num
    unfold J
    rw [hratio]
    linear_combination (-X - X ^ 2) * hhalf

private theorem product_coeff (n : ℕ) :
    coeff n (H * B) = b n + ∑ j ∈ Finset.range n, h (j + 1) * b (n - (j + 1)) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i H * coeff j B), Finset.sum_range_succ']
  simp [H, h, b, add_comm]

private theorem b_nonneg (n : ℕ) : 0 ≤ b n := by
  have h₀ : b 0 = 1 := by
    have hz := congrArg (coeff 0) product
    rw [product_coeff] at hz
    norm_num [coeff_X, coeff_X_pow] at hz
    exact hz
  have h₁ : b 1 = 3 / 2 := by
    have hz := congrArg (coeff 1) product
    rw [product_coeff] at hz
    norm_num [h_initial.1, Finset.sum_range_succ, coeff_one, coeff_X, coeff_X_pow] at hz
    exact hz
  have h₂ : b 2 = 1 / 2 := by
    have hz := congrArg (coeff 2) product
    rw [product_coeff] at hz
    norm_num [h₀, h_initial.1, h_initial.2.1, Finset.sum_range_succ, coeff_one,
      coeff_X, coeff_X_pow] at hz
    linarith
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hz := congrArg (coeff n) product
    rw [product_coeff] at hz
    by_cases hn : n ≤ 3
    · interval_cases n
      · rw [h₀]; norm_num
      · rw [h₁]; norm_num
      · rw [h₂]; norm_num
      · norm_num [h₀, h₁, h₂, h_initial.1, h_initial.2.1, h_initial.2.2.1,
          Finset.sum_range_succ, coeff_one, coeff_X, coeff_X_pow] at hz
        linarith
    · have hn₀ : n ≠ 0 := by omega
      have hn₁ : n ≠ 1 := by omega
      have hn₃ : n ≠ 3 := by omega
      simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow,
        if_neg hn₀, if_neg hn₁, if_neg hn₃, mul_zero, add_zero, sub_zero] at hz
      have hsum : ∑ j ∈ Finset.range n, h (j + 1) * b (n - (j + 1)) ≤ 0 :=
        Finset.sum_nonpos fun j hj =>
          mul_nonpos_of_nonpos_of_nonneg (h_nonpos _ (by omega))
            (ih _ (by have := Finset.mem_range.mp hj; omega))
      linarith

theorem increasing : StrictMono (a r) := by
  have ha₀ : a r 0 = 1 := by
    change coeff 0 D⁻¹ = 1
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_inv, denominator_constant, inv_one]
  have hstep (n : ℕ) : (3 / 2) * a r n ≤ a r (n + 1) := by
    have hn := b_nonneg (n + 1)
    change 0 ≤ coeff (n + 1) ((1 - C (3 / 2) * X) * D⁻¹) at hn
    rw [linear_coeff] at hn
    exact sub_nonneg.mp hn
  have hpos (n : ℕ) : 0 < a r n := by
    induction n with
    | zero => rw [ha₀]; norm_num
    | succ n ih => linarith [hstep n]
  apply strictMono_nat_of_lt_succ
  intro n
  linarith [hstep n, hpos n]

end A288231Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a288231.main := A288231Proof.increasing
