import OMAStatements.S_oeis_a246396
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

/-! Every term of OEIS A246396 has a neighbor one unit away. -/

namespace OpenMath.A246396

private theorem cos_pos_of_outer (x : ℝ) (hleft : 0 < Real.cos x)
    (hright : 0 < Real.cos (x + 3)) : 0 < Real.cos (x + 1) := by
  let q : ℤ := ⌊(x + Real.pi / 2) / (2 * Real.pi)⌋
  let s : ℝ := (q : ℝ) * (2 * Real.pi)
  let y : ℝ := x - s
  have hperiod : ∀ u : ℝ, Real.cos (u - s) = Real.cos u :=
    fun u => Real.cos_sub_int_mul_two_pi u q
  have hpos : 0 < 2 * Real.pi := by positivity
  have hlo : (q : ℝ) ≤ (x + Real.pi / 2) / (2 * Real.pi) := Int.floor_le _
  have hhi : (x + Real.pi / 2) / (2 * Real.pi) < (q : ℝ) + 1 := Int.lt_floor_add_one _
  have hylo : -(Real.pi / 2) ≤ y := by
    have h := (le_div_iff₀ hpos).mp hlo
    dsimp [y, s]
    linarith
  have hyhi : y < Real.pi + Real.pi / 2 := by
    have h := (div_lt_iff₀ hpos).mp hhi
    rw [add_mul, one_mul] at h
    dsimp [y, s]
    linarith
  have hyl : 0 < Real.cos y := by simpa [y, hperiod] using hleft
  have hyu : y < Real.pi / 2 := by
    by_contra! h
    exact (not_le_of_gt hyl) (Real.cos_nonpos_of_pi_div_two_le_of_le h hyhi.le)
  have hyr : 0 < Real.cos (y + 3) := by
    have h : y + 3 = x + 3 - s := by dsimp [y]; ring
    rwa [h, hperiod]
  have hyplus : y + 3 < Real.pi / 2 := by
    by_contra! h
    have hbound : y + 3 ≤ Real.pi + Real.pi / 2 := by linarith [Real.pi_gt_three]
    exact (not_le_of_gt hyr) (Real.cos_nonpos_of_pi_div_two_le_of_le h hbound)
  have hin := Real.cos_pos_of_mem_Ioo
    (show y + 1 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith, by linarith⟩)
  have hs : y + 1 = x + 1 - s := by dsimp [y]; ring
  simpa only [hs, hperiod] using hin

/-- Membership in A246396 is tested at two consecutive nonnegative integers. -/
def mem (n : ℕ) : Prop := Real.cos (n : ℝ) ≤ 0 ∧ Real.cos (n + 1 : ℝ) ≤ 0

theorem main (n : ℕ) (hn : mem n) :
    (0 < n ∧ mem (n - 1)) ∨ mem (n + 1) := by
  cases n with
  | zero =>
      exfalso
      norm_num [mem] at hn
  | succ n =>
      by_cases h : Real.cos (n : ℝ) ≤ 0
      · exact Or.inl ⟨Nat.succ_pos _, h, by simpa [Nat.cast_succ] using hn.1⟩
      · refine Or.inr ⟨by simpa [Nat.cast_succ] using hn.2, ?_⟩
        apply le_of_not_gt
        intro hr
        have hright : 0 < Real.cos ((n : ℝ) + 3) := by
          simpa [Nat.cast_succ, add_assoc, show (1 : ℝ) + (1 + 1) = 3 by norm_num] using hr
        exact (not_le_of_gt (cos_pos_of_outer n (lt_of_not_ge h) hright))
          (by simpa [Nat.cast_succ] using hn.1)

end OpenMath.A246396

theorem OMA.solution : type_of% @OMA.S_oeis_a246396.main :=
  OpenMath.A246396.main
