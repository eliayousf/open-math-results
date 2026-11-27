import OMAStatements.S_oeis_a303647
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Barker's recurrence for the ceiling iteration in OEIS A303647. -/

namespace OpenMath.A303647

noncomputable abbrev ratio : ℝ := OMA.S_oeis_a303647.ratio


noncomputable abbrev a : ℕ → ℤ := OMA.S_oeis_a303647.a

noncomputable abbrev a301483 : ℕ → ℤ := OMA.S_oeis_a303647.a301483

private noncomputable def cubeRootTwo : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)

private theorem cubeRootTwo_nonneg : 0 ≤ cubeRootTwo := by
  unfold cubeRootTwo
  positivity

private theorem cubeRootTwo_cube : cubeRootTwo ^ (3 : ℕ) = 2 := by
  unfold cubeRootTwo
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem cubeRootTwo_bounds :
    1 + 20 / 77 < cubeRootTwo ∧ cubeRootTwo < 1 + 200 / 769 := by
  constructor
  · apply lt_of_pow_lt_pow_left₀ 3 cubeRootTwo_nonneg
    rw [cubeRootTwo_cube]
    norm_num
  · apply lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0 : ℝ) ≤ 1 + 200 / 769)
    rw [cubeRootTwo_cube]
    norm_num

private theorem ratio_bounds : (769 : ℝ) / 200 < ratio ∧ ratio < 77 / 20 := by
  have hd : 0 < cubeRootTwo - 1 := by linarith [cubeRootTwo_bounds.1]
  change 769 / 200 < 1 / (cubeRootTwo - 1) ∧ 1 / (cubeRootTwo - 1) < 77 / 20
  exact ⟨(lt_div_iff₀ hd).2 (by linarith [cubeRootTwo_bounds.2]),
    (div_lt_iff₀ hd).2 (by linarith [cubeRootTwo_bounds.1])⟩

private theorem ratio_cubic : ratio ^ 3 = 3 * ratio ^ 2 + 3 * ratio + 1 := by
  let d := cubeRootTwo - 1
  have hd : d ≠ 0 := ne_of_gt (by dsimp [d]; linarith [cubeRootTwo_bounds.1])
  have h1 : ratio * d = 1 := by
    change (1 / d) * d = 1
    exact div_mul_cancel₀ _ hd
  have hc : d ^ 3 + 3 * d ^ 2 + 3 * d = 1 := by
    dsimp [d]
    linear_combination cubeRootTwo_cube
  calc
    ratio ^ 3 = ratio ^ 3 * (d ^ 3 + 3 * d ^ 2 + 3 * d) := by rw [hc, mul_one]
    _ = (ratio * d) ^ 3 + 3 * ratio * (ratio * d) ^ 2
        + 3 * ratio ^ 2 * (ratio * d) := by ring
    _ = _ := by rw [h1]; ring

-- Two applications of the error recurrence give coefficients whose sum is at most one.
private theorem stableErrors (b : ℕ → ℝ)
    (hb : ∀ n, b (n + 3) = 3 * b (n + 2) + 3 * b (n + 1) + b n)
    (M : ℝ) (hM : 0 ≤ M)
    (h0 : |b 1 - ratio * b 0| ≤ M) (h1 : |b 2 - ratio * b 1| ≤ M)
    (h2 : |b 3 - ratio * b 2| ≤ M) :
    ∀ n, |b (n + 1) - ratio * b n| ≤ M := by
  let A := ratio - 3
  let B := 1 / ratio
  let e := fun n : ℕ => b (n + 1) - ratio * b n
  have hr : 0 < ratio := by linarith [ratio_bounds.1]
  have hInv : B * ratio = 1 := div_mul_cancel₀ _ hr.ne'
  have hFactor : ratio * A - B = 3 := by
    have hB : B = ratio ^ 2 - 3 * ratio - 3 := by
      apply (div_eq_iff hr.ne').2
      linear_combination -ratio_cubic
    rw [hB]
    dsimp [A]
    ring
  have he (n : ℕ) : e (n + 2) = -A * e (n + 1) - B * e n := by
    change b (n + 3) - ratio * b (n + 2) =
      -A * (b (n + 2) - ratio * b (n + 1)) - B * (b (n + 1) - ratio * b n)
    rw [hb n]
    linear_combination -b (n + 1) * hFactor - b n * hInv
  have ht (n : ℕ) : e (n + 3) = (A ^ 2 - B) * e (n + 1) + A * B * e n := by
    rw [he (n + 1), he n]
    ring
  have haLower : (4 : ℝ) / 5 ≤ A := by dsimp [A]; linarith [ratio_bounds.1]
  have haUpper : A ≤ (9 : ℝ) / 10 := by dsimp [A]; linarith [ratio_bounds.2]
  have haPos : 0 ≤ A := by linarith
  have hbLower : (1 : ℝ) / 4 ≤ B := by
    apply (le_div_iff₀ hr).2
    linarith [ratio_bounds.2]
  have hbUpper : B ≤ (3 : ℝ) / 10 := by
    apply (div_le_iff₀ hr).2
    linarith [ratio_bounds.1]
  have hbPos : 0 ≤ B := by linarith
  have haSqLower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4 / 5) haLower 2
  have haSqUpper := pow_le_pow_left₀ haPos haUpper 2
  have hAB := mul_le_mul haUpper hbUpper hbPos (by norm_num : (0 : ℝ) ≤ 9 / 10)
  have hCoeff : 0 ≤ A ^ 2 - B := by linarith
  have hCoeff' : 0 ≤ A * B := mul_nonneg haPos hbPos
  have hSum : (A ^ 2 - B) + A * B ≤ 1 := by linarith
  have windows (n : ℕ) : |e n| ≤ M ∧ |e (n + 1)| ≤ M ∧ |e (n + 2)| ≤ M := by
    induction n with
    | zero => exact ⟨h0, h1, h2⟩
    | succ n ih =>
      refine ⟨ih.2.1, ih.2.2, ?_⟩
      change |e (n + 3)| ≤ M
      rw [ht]
      calc
        _ ≤ |(A ^ 2 - B) * e (n + 1)| + |(A * B) * e n| := abs_add_le _ _
        _ ≤ (A ^ 2 - B) * M + A * B * M := by
          rw [abs_mul, abs_mul, abs_of_nonneg hCoeff, abs_of_nonneg hCoeff']
          exact add_le_add (mul_le_mul_of_nonneg_left ih.2.1 hCoeff)
            (mul_le_mul_of_nonneg_left ih.1 hCoeff')
        _ = ((A ^ 2 - B) + A * B) * M := by ring
        _ ≤ M := by simpa using mul_le_mul_of_nonneg_right hSum hM
  exact fun n => (windows n).1

private def candidate : ℕ → ℤ
  | 0 => 1
  | 1 => 5
  | 2 => 21
  | n + 3 => 3 * candidate (n + 2) + 3 * candidate (n + 1) + candidate n + 3

private theorem candidate_ceil (n : ℕ) :
    candidate (n + 1) = ⌈ratio * (candidate n : ℝ) + 1⌉ := by
  -- This shift removes the constant term in the affine recurrence.
  let b := fun n : ℕ => 2 * (candidate n : ℝ) + 1
  have hb (k : ℕ) : b (k + 3) = 3 * b (k + 2) + 3 * b (k + 1) + b k := by
    simp only [b, candidate, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    ring
  have h0 : |b 1 - ratio * b 0| ≤ (3 : ℝ) / 4 := by
    norm_num [b, candidate, abs_le]
    constructor <;> linarith [ratio_bounds.1, ratio_bounds.2]
  have h1 : |b 2 - ratio * b 1| ≤ (3 : ℝ) / 4 := by
    norm_num [b, candidate, abs_le]
    constructor <;> linarith [ratio_bounds.1, ratio_bounds.2]
  have h2 : |b 3 - ratio * b 2| ≤ (3 : ℝ) / 4 := by
    norm_num [b, candidate, abs_le]
    constructor <;> linarith [ratio_bounds.1, ratio_bounds.2]
  have h := abs_le.mp (stableErrors b hb _ (by norm_num) h0 h1 h2 n)
  change -(3 / 4 : ℝ) ≤
      (2 * (candidate (n + 1) : ℝ) + 1) - ratio * (2 * (candidate n : ℝ) + 1) ∧
    (2 * (candidate (n + 1) : ℝ) + 1) - ratio * (2 * (candidate n : ℝ) + 1)
      ≤ 3 / 4 at h
  symm
  rw [Int.ceil_eq_iff]
  constructor <;> linarith [h.1, h.2, ratio_bounds.1, ratio_bounds.2]

private theorem a_succ_candidate (n : ℕ) : a (n + 1) = candidate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ⌈ratio * (a (n + 1) : ℝ) + 1⌉ = candidate (n + 1)
    rw [ih, ← candidate_ceil]

theorem a_initial : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 5 ∧ a 3 = 21 ∧ a 4 = 82 :=
  ⟨rfl, rfl, a_succ_candidate 1, a_succ_candidate 2, a_succ_candidate 3⟩

theorem affineRecurrence (n : ℕ) :
    a (n + 4) = 3 * a (n + 3) + 3 * a (n + 2) + a (n + 1) + 3 := by
  change a ((n + 3) + 1) =
    3 * a ((n + 2) + 1) + 3 * a ((n + 1) + 1) + a (n + 1) + 3
  simp only [a_succ_candidate, candidate]

theorem fourthOrderRecurrence (n : ℕ) (hn : 4 < n) :
    a n = 4 * a (n - 1) - 2 * a (n - 3) - a (n - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 5 := ⟨n - 5, by omega⟩
  have h₁ := affineRecurrence k
  have h₂ : a (k + 5) = 3 * a (k + 4) + 3 * a (k + 3) + a (k + 2) + 3 :=
    affineRecurrence (k + 1)
  rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 3 = k + 2 by omega,
    show k + 5 - 4 = k + 1 by omega]
  omega

private def floorCandidate : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | 2 => 11
  | n + 3 => 3 * floorCandidate (n + 2) + 3 * floorCandidate (n + 1) + floorCandidate n - 1

private theorem candidate_floor (n : ℕ) :
    floorCandidate (n + 1) = ⌊ratio * (floorCandidate n : ℝ)⌋ := by
  -- The floor candidate has a different affine constant and hence a different shift.
  let b := fun n : ℕ => 6 * (floorCandidate n : ℝ) - 1
  have hb (k : ℕ) : b (k + 3) = 3 * b (k + 2) + 3 * b (k + 1) + b k := by
    simp only [b, floorCandidate, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
      Int.cast_one]
    ring
  have h0 : |b 1 - ratio * b 0| ≤ (23 : ℝ) / 10 := by
    norm_num [b, floorCandidate, abs_le]
    constructor <;> linarith [ratio_bounds.1, ratio_bounds.2]
  have h1 : |b 2 - ratio * b 1| ≤ (23 : ℝ) / 10 := by
    norm_num [b, floorCandidate, abs_le]
    constructor <;> linarith [ratio_bounds.1, ratio_bounds.2]
  have h2 : |b 3 - ratio * b 2| ≤ (23 : ℝ) / 10 := by
    norm_num [b, floorCandidate, abs_le]
    constructor <;> linarith [ratio_bounds.1, ratio_bounds.2]
  have h := abs_le.mp (stableErrors b hb _ (by norm_num) h0 h1 h2 n)
  change -(23 / 10 : ℝ) ≤
      (6 * (floorCandidate (n + 1) : ℝ) - 1) - ratio * (6 * (floorCandidate n : ℝ) - 1) ∧
    (6 * (floorCandidate (n + 1) : ℝ) - 1) - ratio * (6 * (floorCandidate n : ℝ) - 1)
      ≤ 23 / 10 at h
  symm
  rw [Int.floor_eq_iff]
  constructor <;> linarith [h.1, h.2, ratio_bounds.1, ratio_bounds.2]

private theorem a301483_succ_candidate (n : ℕ) : a301483 (n + 1) = floorCandidate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ⌊ratio * (a301483 (n + 1) : ℝ)⌋ = floorCandidate (n + 1)
    rw [ih, ← candidate_floor]

theorem a301483_initial :
    a301483 0 = 0 ∧ a301483 1 = 1 ∧ a301483 2 = 3 ∧ a301483 3 = 11 ∧ a301483 4 = 42 :=
  ⟨rfl, rfl, a301483_succ_candidate 1, a301483_succ_candidate 2, a301483_succ_candidate 3⟩

theorem floorAffineRecurrence (n : ℕ) :
    a301483 (n + 4) =
      3 * a301483 (n + 3) + 3 * a301483 (n + 2) + a301483 (n + 1) - 1 := by
  change a301483 ((n + 3) + 1) =
    3 * a301483 ((n + 2) + 1) + 3 * a301483 ((n + 1) + 1) + a301483 (n + 1) - 1
  simp only [a301483_succ_candidate, floorCandidate]

theorem floorFourthOrderRecurrence (n : ℕ) (hn : 4 < n) :
    a301483 n = 4 * a301483 (n - 1) - 2 * a301483 (n - 3) - a301483 (n - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 5 := ⟨n - 5, by omega⟩
  have h₁ := floorAffineRecurrence k
  have h₂ : a301483 (k + 5) =
      3 * a301483 (k + 4) + 3 * a301483 (k + 3) + a301483 (k + 2) - 1 :=
    floorAffineRecurrence (k + 1)
  rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 3 = k + 2 by omega,
    show k + 5 - 4 = k + 1 by omega]
  omega

open PowerSeries

private noncomputable abbrev Xz : ℤ⟦X⟧ := PowerSeries.X

private noncomputable def D : ℤ⟦X⟧ := 1 - 4 * Xz + 2 * Xz ^ 3 + Xz ^ 4

private theorem series_of_recurrence (f : ℕ → ℤ)
    (step : ∀ n, f (n + 4) = 4 * f (n + 3) - 2 * f (n + 1) - f n) :
    D * PowerSeries.mk f =
      f 0 • (1 : ℤ⟦X⟧) + (f 1 - 4 * f 0) • Xz + (f 2 - 4 * f 1) • Xz^2 +
        (f 3 - 4 * f 2 + 2 * f 0) • Xz^3 := by
  rw [show D * PowerSeries.mk f =
      PowerSeries.mk f - (4 : ℤ) • (Xz^1 * PowerSeries.mk f) +
        (2 : ℤ) • (Xz^3 * PowerSeries.mk f) + Xz^4 * PowerSeries.mk f by
    simp only [D, pow_one, zsmul_eq_mul]
    ring]
  ext n
  simp only [map_add, map_sub, map_zsmul, coeff_X_pow_mul', coeff_mk,
    coeff_one, coeff_X, coeff_X_pow]
  by_cases h : n < 4
  · interval_cases n <;> norm_num
  · have hs := step (n - 4)
    simp only [show n - 4 + 4 = n by omega,
      show n - 4 + 3 = n - 1 by omega,
      show n - 4 + 1 = n - 3 by omega] at hs
    simp only [show 1 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega, if_true, if_false, smul_zero, add_zero, zsmul_eq_mul]
    rw [hs]
    ring

private theorem finish (u d q r : ℕ → ℤ)
    (u0 : u 0 = 0) (u1 : u 1 = 1) (u2 : u 2 = 5) (u3 : u 3 = 21)
    (d0 : d 0 = 0) (d1 : d 1 = 1) (d2 : d 2 = 3) (d3 : d 3 = 11)
    (q0 : q 0 = 1) (q1 : q 1 = 1) (q2 : q 2 = 3) (q3 : q 3 = 10)
    (r0 : r 0 = 1) (r1 : r 1 = 4) (r2 : r 2 = 16) (r3 : r 3 = 62)
    (ustep : ∀ n, u (n + 4) = 4 * u (n + 3) - 2 * u (n + 1) - u n)
    (dstep : ∀ n, d (n + 4) = 4 * d (n + 3) - 2 * d (n + 1) - d n)
    (qstep : ∀ n, q (n + 4) = 4 * q (n + 3) - 2 * q (n + 1) - q n)
    (rstep : ∀ n, r (n + 4) = 4 * r (n + 3) - 2 * r (n + 1) - r n) :
    (∀ n : ℕ, 2 < n → u n = d (n + 2) - q (n + 2) + r (n - 3)) ∧
    ((1 - Xz) * (1 - 3 * Xz - 3 * Xz ^ 2 - Xz ^ 3) *
      PowerSeries.mk u = Xz * (1 + Xz + Xz ^ 2)) ∧
    (∀ n : ℕ, 4 < n → u n = 4 * u (n - 1) - 2 * u (n - 3) - u (n - 4)) := by
  have hU : D * PowerSeries.mk u = Xz * (1 + Xz + Xz ^ 2) := by
    rw [series_of_recurrence u ustep, u0, u1, u2, u3]
    norm_num [zsmul_eq_mul]
    ring
  have hL : D * PowerSeries.mk d = Xz * (1 - Xz - Xz ^ 2) := by
    rw [series_of_recurrence d dstep, d0, d1, d2, d3]
    norm_num [zsmul_eq_mul]
    ring
  have hQ : D * PowerSeries.mk q = 1 - 3 * Xz - Xz ^ 2 := by
    rw [series_of_recurrence q qstep, q0, q1, q2, q3]
    norm_num [zsmul_eq_mul]
    ring
  have hR : D * PowerSeries.mk r = 1 := by
    rw [series_of_recurrence r rstep, r0, r1, r2, r3]
    norm_num [zsmul_eq_mul]
  have hD : IsUnit D := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [D]
  have hshift : PowerSeries.mk d - PowerSeries.mk q + Xz ^ 5 * PowerSeries.mk r =
      Xz ^ 2 * PowerSeries.mk u - 1 := hD.mul_left_cancel (by
    calc
      _ = D * PowerSeries.mk d - D * PowerSeries.mk q + Xz ^ 5 * (D * PowerSeries.mk r) := by ring
      _ = Xz ^ 2 * (D * PowerSeries.mk u) - D := by rw [hL, hQ, hR, hU]; unfold D; ring
      _ = _ := by ring)
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have h := congrArg (PowerSeries.coeff (n + 2)) hshift
    simp only [map_add, map_sub, coeff_mk, coeff_X_pow_mul', coeff_one,
      show 5 ≤ n + 2 by omega, show 2 ≤ n + 2 by omega,
      show n + 2 ≠ 0 by omega, if_true, if_false, add_tsub_cancel_right] at h
    rw [show n + 2 - 5 = n - 3 by omega] at h
    omega
  · convert hU using 1
    unfold D
    ring
  · intro n hn
    have hs := ustep (n - 4)
    simpa only [show n - 4 + 4 = n by omega,
      show n - 4 + 3 = n - 1 by omega, show n - 4 + 1 = n - 3 by omega] using hs

-- Coefficients of (1 - 3X - X^2)/(1 - 4X + 2X^3 + X^4).
noncomputable abbrev a195350 : ℕ → ℤ := OMA.S_oeis_a303647.a195350

-- Coefficients of 1/(1 - 4X + 2X^3 + X^4).
noncomputable abbrev a195339 : ℕ → ℤ := OMA.S_oeis_a303647.a195339

theorem main :
    (∀ n : ℕ, 2 < n → a n = a301483 (n + 2) - a195350 (n + 2) + a195339 (n - 3)) ∧
    ((1 - PowerSeries.X) * (1 - 3 * PowerSeries.X - 3 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3) *
      PowerSeries.mk a = PowerSeries.X * (1 + PowerSeries.X + PowerSeries.X ^ 2)) ∧
    (∀ n : ℕ, 4 < n → a n = 4 * a (n - 1) - 2 * a (n - 3) - a (n - 4)) := by
  obtain ⟨u0, u1, u2, u3, u4⟩ := a_initial
  obtain ⟨d0, d1, d2, d3, d4⟩ := a301483_initial
  refine finish a a301483 a195350 a195339
    u0 u1 u2 u3 d0 d1 d2 d3 rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · intro n
    by_cases hn : n = 0
    · subst n
      norm_num [u0, u1, u3, u4]
    · simpa only [show n + 4 - 1 = n + 3 by omega,
        show n + 4 - 3 = n + 1 by omega, Nat.add_sub_cancel] using
        fourthOrderRecurrence (n + 4) (by omega)
  · intro n
    by_cases hn : n = 0
    · subst n
      norm_num [d0, d1, d3, d4]
    · simpa only [show n + 4 - 1 = n + 3 by omega,
        show n + 4 - 3 = n + 1 by omega, Nat.add_sub_cancel] using
        floorFourthOrderRecurrence (n + 4) (by omega)
  · intro n
    rfl
  · intro n
    rfl

end OpenMath.A303647

theorem OMA.solution : type_of% @OMA.S_oeis_a303647.main := OpenMath.A303647.main
