import OMAStatements.S_oeis_a048625
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The recurrence and continued fraction for the tie-down Pisot sequence in OEIS A048625. -/

namespace OpenMath.A048625

noncomputable abbrev a : ℕ → ℤ := OMA.S_oeis_a048625.a

private def candidate : ℕ → ℤ
  | 0 => 4
  | 1 => 6
  | 2 => 9
  | n + 3 => candidate (n + 2) + candidate n

private theorem candidate_step (n : ℕ) :
    candidate (n + 3) = candidate (n + 2) + candidate n := by
  rw [candidate]

private theorem candidate_pos_mono (n : ℕ) :
    0 < candidate n ∧ candidate n < candidate (n + 1) ∧
      candidate (n + 1) < candidate (n + 2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    refine ⟨lt_trans ih.1 ih.2.1, ih.2.2, ?_⟩
    change candidate (n + 2) < candidate (n + 3)
    rw [candidate_step]
    omega

private def defect (n : ℕ) : ℤ :=
  candidate (n + 1) ^ 2 - candidate n * candidate (n + 2)

-- The determinant of a pair of consecutive entries has its own linear recurrence.
private theorem defect_step (n : ℕ) :
    defect (n + 3) = defect n - defect (n + 1) := by
  unfold defect
  rw [show n + 3 + 2 = (n + 2) + 3 by omega, candidate_step (n + 2),
    show n + 3 + 1 = (n + 1) + 3 by omega, candidate_step (n + 1),
    show n + 1 + 2 = n + 3 by omega, candidate_step n]
  ring

private theorem strictBounds (n : ℕ) : |2 * defect (n + 2)| < candidate (n + 2) := by
  have window (k : ℕ) : |2 * defect (k + 2)| < candidate (k + 2) ∧
      |2 * defect (k + 3)| < candidate (k + 3) ∧
      |2 * defect (k + 4)| < candidate (k + 4) := by
    induction k with
    | zero => decide
    | succ k ih =>
      refine ⟨ih.2.1, ih.2.2, ?_⟩
      change |2 * defect ((k + 2) + 3)| < candidate ((k + 2) + 3)
      rw [defect_step, mul_sub, candidate_step]
      change |2 * defect (k + 2) - 2 * defect (k + 3)| <
        candidate (k + 4) + candidate (k + 2)
      have h₁ := abs_lt.mp ih.1
      have h₂ := abs_lt.mp ih.2.1
      have h₃ : candidate (k + 3) < candidate (k + 4) := (candidate_pos_mono (k + 3)).2.1
      apply abs_lt.mpr
      constructor <;> omega
  exact (window n).1

private theorem roundingBounds (n : ℕ) :
    -candidate n < 2 * defect n ∧ 2 * defect n ≤ candidate n := by
  rcases n with _ | n
  · decide
  rcases n with _ | n
  · decide
  exact ⟨(abs_lt.mp (strictBounds n)).1, (abs_lt.mp (strictBounds n)).2.le⟩

private theorem rounding (n : ℕ) :
    ⌈(candidate (n + 1) : ℚ) ^ 2 / (candidate n : ℚ) - 1 / 2⌉ =
      candidate (n + 2) := by
  have hpos : (0 : ℚ) < (candidate n : ℚ) := by exact_mod_cast (candidate_pos_mono n).1
  have hl : -(candidate n : ℚ) <
      2 * ((candidate (n + 1) : ℚ) ^ 2 - (candidate n : ℚ) * candidate (n + 2)) := by
    exact_mod_cast (show -candidate n < 2 *
        (candidate (n + 1) ^ 2 - candidate n * candidate (n + 2)) from (roundingBounds n).1)
  have hu : 2 * ((candidate (n + 1) : ℚ) ^ 2 - (candidate n : ℚ) * candidate (n + 2))
      ≤ (candidate n : ℚ) := by
    exact_mod_cast (show 2 *
        (candidate (n + 1) ^ 2 - candidate n * candidate (n + 2)) ≤ candidate n
      from (roundingBounds n).2)
  apply Int.ceil_eq_iff.mpr
  constructor
  · have h := (lt_div_iff₀ hpos).2
      (show ((candidate (n + 2) : ℚ) - 1 / 2) * (candidate n : ℚ) <
        (candidate (n + 1) : ℚ) ^ 2 by linarith)
    linarith
  · have h := (div_le_iff₀ hpos).2
      (show (candidate (n + 1) : ℚ) ^ 2 ≤
        ((candidate (n + 2) : ℚ) + 1 / 2) * (candidate n : ℚ) by linarith)
    linarith

private theorem a_eq_candidate (n : ℕ) : a n = candidate n := by
  have window (k : ℕ) : a k = candidate k ∧ a (k + 1) = candidate (k + 1) := by
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      change ⌈(a (k + 1) : ℚ) ^ 2 / (a k : ℚ) - 1 / 2⌉ = candidate (k + 2)
      rw [ih.1, ih.2]
      exact rounding k
  exact (window n).1

theorem a_initial : a 0 = 4 ∧ a 1 = 6 ∧ a 2 = 9 :=
  ⟨rfl, rfl, a_eq_candidate 2⟩

theorem recurrence (n : ℕ) : a (n + 3) = a (n + 2) + a n := by
  simp only [a_eq_candidate, candidate_step]

open PowerSeries

noncomputable abbrev TailFamily : (ℕ → ℚ⟦X⟧) → Prop := OMA.S_oeis_a048625.TailFamily

private noncomputable abbrev Xr : ℚ⟦X⟧ := X

private noncomputable def L (k : ℕ) : ℚ⟦X⟧ := C (2 * (k : ℚ) + 1) * Xr + Xr ^ 3

private noncomputable def D (k : ℕ) : ℚ⟦X⟧ := 1 - L k

private theorem linear_succ (k : ℕ) : L (k + 1) = L k + 2 * Xr := by
  unfold L
  push_cast
  rw [show (2 : ℚ) * ((k : ℚ) + 1) + 1 = (2 * (k : ℚ) + 1) + 2 by ring]
  simp only [map_add, map_ofNat]
  ring

private theorem const_D (k : ℕ) : constantCoeff (D k) = 1 := by
  simp [D, L]

private theorem unit_D (k : ℕ) : IsUnit (D k) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, const_D]
  exact isUnit_one

private noncomputable def Qclosed (k : ℕ) : ℚ⟦X⟧ := 1 + 2 * Xr * (D k)⁻¹

private theorem Qclosed_mul_D (k : ℕ) : Qclosed k * D k = D k + 2 * Xr := by
  rw [Qclosed, add_mul, one_mul, mul_assoc, PowerSeries.inv_mul_cancel (D k) (by simp [const_D]),
    mul_one]

private theorem tail_equation {Q : ℕ → ℚ⟦X⟧} (hQ : TailFamily Q) (k : ℕ) :
    Q k * Q (k + 1) = (1 + L (k + 1)) * Q (k + 1) - L k := by
  rw [show 1 + L (k + 1) = 1 + Xr ^ 3 + C (2 * (k : ℚ) + 3) * Xr by
    unfold L
    push_cast
    rw [show (2 : ℚ) * ((k : ℚ) + 1) + 1 = 2 * (k : ℚ) + 3 by ring]
    ring]
  rw [show L k = Xr * (C (2 * (k : ℚ) + 1) + Xr ^ 2) by unfold L; ring]
  exact (hQ k).2

private theorem closed_tail_family : TailFamily Qclosed := by
  intro k
  constructor
  · simp [Qclosed]
  · rw [show (1 + Xr ^ 3 + C (2 * (k : ℚ) + 3) * Xr) = 1 + L (k + 1) by
      unfold L
      push_cast
      rw [show (2 : ℚ) * ((k : ℚ) + 1) + 1 = 2 * (k : ℚ) + 3 by ring]
      ring]
    rw [show Xr * (C (2 * (k : ℚ) + 1) + Xr ^ 2) = L k by unfold L; ring]
    apply (unit_D (k + 1)).mul_right_cancel
    have hnext : Qclosed (k + 1) * D (k + 1) = D k := by
      rw [Qclosed_mul_D, D, linear_succ, D]
      ring
    calc
      _ = Qclosed k * D k := by rw [mul_assoc, hnext]
      _ = D k + 2 * Xr := Qclosed_mul_D k
      _ = (1 + L (k + 1)) * D k - L k * D (k + 1) := by
        simp only [D, linear_succ]
        ring
      _ = _ := by rw [sub_mul, mul_assoc, hnext]

private theorem tails_unique {Q R : ℕ → ℚ⟦X⟧} (hQ : TailFamily Q) (hR : TailFamily R) : Q = R := by
  have hdiv (n : ℕ) : ∀ k, Xr ^ n ∣ Q k - R k := by
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      have hu : IsUnit (Q (k + 1)) := by
        rw [PowerSeries.isUnit_iff_constantCoeff, (hQ (k + 1)).1]
        exact isUnit_one
      apply hu.dvd_mul_right.mp
      rw [show (Q k - R k) * Q (k + 1) =
          (1 + L (k + 1) - R k) * (Q (k + 1) - R (k + 1)) by
        linear_combination tail_equation hQ k - tail_equation hR k]
      have hx : Xr ∣ 1 + L (k + 1) - R k := by
        apply PowerSeries.X_dvd_iff.2
        simp [L, (hR k).1]
      simpa only [pow_succ, mul_comm Xr] using (mul_dvd_mul hx (ih (k + 1)))
  funext k
  apply sub_eq_zero.mp
  ext n
  have hz := PowerSeries.X_pow_dvd_iff.mp (hdiv (n + 1) k) n (Nat.lt_succ_self n)
  simpa using hz

private theorem series_recurrence (f : ℕ → ℤ) (h0 : f 0 = 4) (h1 : f 1 = 6) (h2 : f 2 = 9)
    (hstep : ∀ n : ℕ, f (n + 3) = f (n + 2) + f n) :
    D 0 * PowerSeries.mk (fun n => (f n : ℚ)) = 4 + 2 * Xr + 3 * Xr ^ 2 := by
  let S : ℚ⟦X⟧ := PowerSeries.mk (fun n => (f n : ℚ))
  change D 0 * S = _
  rw [show D 0 * S = S - Xr ^ 1 * S - Xr ^ 3 * S by simp [D, L]; ring]
  rw [show (4 + 2 * Xr + 3 * Xr ^ 2 : ℚ⟦X⟧) =
      C 4 + C 2 * Xr + C 3 * Xr ^ 2 by simp only [map_ofNat]]
  rw [show (C (2:ℚ) * Xr : ℚ⟦X⟧) = C 2 * Xr ^ 1 by simp]
  ext n
  simp only [map_add, map_sub, coeff_X_pow_mul', coeff_C, coeff_C_mul_X_pow, S, coeff_mk]
  by_cases hn : n < 3
  · interval_cases n <;> norm_num [h0, h1, h2]
  · have hs := hstep (n - 3)
    simp only [show n - 3 + 3 = n by omega, show n - 3 + 2 = n - 1 by omega] at hs
    simp only [show 1 ≤ n by omega, show 3 ≤ n by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, if_true, if_false, add_zero]
    rw [hs]
    push_cast
    ring

theorem continued_fraction (f : ℕ → ℤ) (h0 : f 0 = 4) (h1 : f 1 = 6) (h2 : f 2 = 9)
    (hstep : ∀ n : ℕ, f (n + 3) = f (n + 2) + f n) :
    ∃ Q : ℕ → ℚ⟦X⟧, TailFamily Q ∧ (∀ R, TailFamily R → R = Q) ∧
      X ^ 6 * PowerSeries.mk (fun n => (f n : ℚ)) =
        (1 / 2 : ℚ) • (Q 0 - 1) - (X + X ^ 2 + X ^ 3 + 2 * X ^ 4 + 3 * X ^ 5) := by
  refine ⟨Qclosed, closed_tail_family, fun R hR => tails_unique hR closed_tail_family, ?_⟩
  apply (unit_D 0).mul_left_cancel
  have hhalf : D 0 * ((1 / 2 : ℚ) • (Qclosed 0 - 1)) = Xr := by
    rw [PowerSeries.smul_eq_C_mul]
    calc
      _ = C (1 / 2 : ℚ) * (Qclosed 0 * D 0 - D 0) := by ring
      _ = C (1 / 2 : ℚ) * (2 * Xr) := by rw [Qclosed_mul_D]; ring
      _ = _ := by
        rw [← mul_assoc, show C (1 / 2 : ℚ) * (2 : ℚ⟦X⟧) = 1 by
          calc
            _ = C ((1 / 2 : ℚ) * 2) := by simp only [map_mul, map_ofNat]
            _ = _ := by norm_num, one_mul]
  rw [show D 0 * (Xr ^ 6 * PowerSeries.mk (fun n => (f n : ℚ))) =
      Xr ^ 6 * (D 0 * PowerSeries.mk (fun n => (f n : ℚ))) by ring,
    series_recurrence f h0 h1 h2 hstep, mul_sub, hhalf]
  simp [D, L]
  ring

theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = a (n - 1) + a (n - 3)) ∧
    ∃ Q : ℕ → ℚ⟦X⟧, TailFamily Q ∧ (∀ R, TailFamily R → R = Q) ∧
      X ^ 6 * PowerSeries.mk (fun n => (a n : ℚ)) =
        (1 / 2 : ℚ) • (Q 0 - 1) - (X + X ^ 2 + X ^ 3 + 2 * X ^ 4 + 3 * X ^ 5) := by
  constructor
  · intro n hn
    have h := recurrence (n - 3)
    simpa only [show n - 3 + 3 = n by omega, show n - 3 + 2 = n - 1 by omega] using h
  · obtain ⟨h0, h1, h2⟩ := a_initial
    exact continued_fraction a h0 h1 h2 recurrence

end OpenMath.A048625

theorem OMA.solution : type_of% @OMA.S_oeis_a048625.main := OpenMath.A048625.main
