import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Set.Finite.Basic

/-!
# The gaps in the OEIS A351415 Beatty intersection

Source: https://oeis.org/A351415/internal

The two Beatty slopes are the golden ratio and the square root of five, with
positive integer indices. The allowed gaps are precisely 2 through 6. Every
one of these gaps occurs for infinitely many starting values.
-/

namespace OMA.S_oeis_a351415

noncomputable def alpha : ℝ := (Real.sqrt 5 - 1) / 2

def InBeatty (r : ℝ) (m : ℤ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ⌊(k : ℝ) * r⌋ = m

def Mem (m : ℤ) : Prop :=
  InBeatty (alpha + 1) m ∧ InBeatty (Real.sqrt 5) m

def Consecutive (x y : ℤ) : Prop :=
  x < y ∧ Mem x ∧ Mem y ∧ ∀ z : ℤ, x < z → z < y → ¬Mem z

theorem main :
    (∀ x y : ℤ, Consecutive x y → 2 ≤ y - x ∧ y - x ≤ 6) ∧
    (∀ g : ℤ, 2 ≤ g → g ≤ 6 → {x : ℤ | Consecutive x (x+g)}.Infinite) := by
  sorry

end OMA.S_oeis_a351415
