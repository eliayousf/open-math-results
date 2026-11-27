import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Spezia's characteristic coefficient conjecture for OEIS A001752. -/

namespace OMA.S_oeis_a001752

/-- A001752, using Hurt's weighted sum formula from the OEIS entry. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 4), (n + 3 - i) * ((i ^ 2 / 2) / 2)

/-- The top-left square of Spezia's array described in A010751. -/
def speziaMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => ((j.val : ℤ) - i.val + 1) / 2

theorem main : ∀ n : ℕ, 2 < n →
    |(speziaMatrix n).charpoly.coeff (n - 2)| = (a (n - 3) : ℤ) := by
  sorry

end OMA.S_oeis_a001752
