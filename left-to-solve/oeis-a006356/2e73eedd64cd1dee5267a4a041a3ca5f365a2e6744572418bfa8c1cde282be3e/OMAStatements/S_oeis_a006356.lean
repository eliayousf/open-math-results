import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Totient

/-!
# The asymptotic leading coefficient of the k-glass sequence

Source: https://oeis.org/A006356
Credit: @Assassino9931

The statement combines the asymptotic in Benoît Cloitre's comment with its
conjecture about the leading coefficient. Paul D. Hanna's generating function
specifies the sequence with index zero. The positive plate-count range includes
one plate, where the generating function is `1 / (1 - X)`.
-/

namespace OMA.S_oeis_a006356

open scoped Asymptotics

/-- Hanna's polynomial `F_k` evaluated at `s * X`. -/
def glassPolynomial (k : ℕ) (s : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun j =>
    if j ≤ k then
      (-1 : ℚ) ^ ((j + 1) / 2) * (((k + j) / 2).choose j : ℚ) * s ^ j
    else 0

/-- Coefficients of the generating function `F_(k-1)(-X) / F_k(X)`. -/
noncomputable def glassSequence (k n : ℕ) : ℚ :=
  PowerSeries.coeff n (glassPolynomial (k - 1) (-1) * (glassPolynomial k 1)⁻¹)

noncomputable def growthRate (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) / Real.cos ((k : ℝ) * Real.pi / (2 * (k : ℝ) + 1))

theorem main : ∀ k : ℕ, 0 < k → ∃ z : ℝ,
    (fun n : ℕ => (glassSequence k n : ℝ)) ~[Filter.atTop] (fun n => z * growthRate k ^ n) ∧
    1 < z ∧ z < 2 ∧
    ∃ p : Polynomial ℤ, p.natDegree = Nat.totient (2 * k + 1) / 2 ∧
      p.eval₂ (Int.castRingHom ℝ) z = 0 := by
  sorry

end OMA.S_oeis_a006356
