import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Adjacent terms of OEIS A246396

Harvey P. Dale's conjecture that every term has a neighbor one unit away.
Source: https://oeis.org/A246396
-/

namespace OMA.S_oeis_a246396

def Mem (n : ℕ) : Prop :=
  Real.cos (n : ℝ) ≤ 0 ∧ Real.cos (n + 1 : ℝ) ≤ 0

theorem main : ∀ n : ℕ, Mem n → (0 < n ∧ Mem (n - 1)) ∨ Mem (n + 1) := by
  sorry

end OMA.S_oeis_a246396
