import Mathlib.Algebra.BigOperators.Ring.List

/-! The recurrence for the scaled sum of the source rational finite sets.
Source: https://oeis.org/A264200/internal
At generation n+1 the list entries are the source values multiplied by b^n.
Translation is injective and has output at least one before scaling.
Eligible division is injective and has output less than one before scaling.
Thus the list enumerates the source set without multiplicity. -/

namespace OMA.S_oeis_a264200

def scale (b : ℤ) (n : ℕ) := b ^ n

/-- Scaled numerators of the values in generation n+1. -/
def values (b : ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => (values b n).map (fun x => b * (x + scale b n)) ++
      (values b n).filter (fun x => x < b * scale b n)

def sumVal (b : ℤ) (n : ℕ) := (values b n).sum

/-- The sum multiplied by the source denominator b^(n-1). -/
def a (b : ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumVal b n

theorem main : ∀ n : ℕ, 4 ≤ n →
    a 2 n = 3 * a 2 (n - 1) + 4 * a 2 (n - 2) - 8 * a 2 (n - 3) - 8 * a 2 (n - 4) := by
  sorry

end OMA.S_oeis_a264200
