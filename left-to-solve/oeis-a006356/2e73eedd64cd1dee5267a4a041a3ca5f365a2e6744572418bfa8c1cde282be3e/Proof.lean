import OMAStatements.S_oeis_a006356
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

open OMA.S_oeis_a006356 PowerSeries Filter Asymptotics in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a006356.main) := by
  intro h
  have h0 : glassPolynomial 0 (-1) = 1 := by
    ext n
    cases n with
    | zero => norm_num [glassPolynomial]
    | succ n => simp [glassPolynomial, coeff_one]
  have h1 : glassPolynomial 1 1 = 1 - (X : PowerSeries ℚ) := by
    ext n
    rcases n with _ | _ | n
    · norm_num [glassPolynomial, coeff_X]
    · norm_num [glassPolynomial, coeff_X]
    · have hn : ¬ n.succ.succ ≤ 1 := by omega
      simp [glassPolynomial, hn, coeff_one, coeff_X]
  have hinv : (1 - (X : PowerSeries ℚ))⁻¹ = PowerSeries.mk 1 := by
    apply (PowerSeries.inv_eq_iff_mul_eq_one (by simp)).mpr
    exact PowerSeries.mk_one_mul_one_sub_eq_one ℚ
  have hseq (n : ℕ) : glassSequence 1 n = 1 := by
    unfold glassSequence
    rw [show 1 - 1 = (0 : ℕ) by decide, h0, h1, one_mul, hinv, coeff_mk]
    rfl
  have hgrowth : growthRate 1 = 1 := by
    unfold growthRate
    norm_num [Real.cos_pi_div_three]
  obtain ⟨z, hz, hlt, _⟩ := h 1 (by decide)
  have hequiv : Asymptotics.IsEquivalent atTop (Function.const ℕ (1 : ℝ))
      (Function.const ℕ z) := by
    change Asymptotics.IsEquivalent atTop (fun _ : ℕ => (1 : ℝ)) (fun _ => z)
    simpa only [hseq, Rat.cast_one, hgrowth, one_pow, mul_one] using hz
  have heq := tendsto_nhds_unique
    (tendsto_const_nhds : Tendsto (Function.const ℕ (1 : ℝ)) atTop (nhds 1))
    hequiv.tendsto_const
  exact (ne_of_lt hlt) heq
