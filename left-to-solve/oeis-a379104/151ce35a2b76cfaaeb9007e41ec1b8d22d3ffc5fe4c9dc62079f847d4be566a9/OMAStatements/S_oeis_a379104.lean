import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Finset.Range

/-!
# Homogeneous recurrences for elementary symmetric Fibonacci and Lucas sums

Source: https://oeis.org/A379104/internal
The order is indexed by the symmetric degree `k`, as in the listed orders for
`k = 2, 3, 4, 5, 6`. The positive distinct Fibonacci sequence starts at 1, 2,
and the Lucas sequence starts at 2, 1 as in A000032.
-/

namespace OMA.S_oeis_a379104

open Polynomial

def a : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => a n + a (n + 1)

def b : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => b n + b (n + 1)

noncomputable def elementary (u : ℕ → ℤ) (k n : ℕ) : ℤ :=
  (∏ i ∈ Finset.range n, (1 + C (u i) * X : Polynomial ℤ)).coeff k

def IsRecurrence (p : Polynomial ℤ) (u : ℕ → ℤ) (k : ℕ) : Prop :=
  ∀ n : ℕ, ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * elementary u k (n + i) = 0

theorem main : ∀ k : ℕ, 1 ≤ k →
    ∃ p : Polynomial ℤ,
      p.Monic ∧ p.natDegree = (k + 1) * (k + 2) / 2 ∧ p.coeff 0 ≠ 0 ∧
      IsRecurrence p a k ∧ IsRecurrence p b k := by
  sorry

end OMA.S_oeis_a379104
