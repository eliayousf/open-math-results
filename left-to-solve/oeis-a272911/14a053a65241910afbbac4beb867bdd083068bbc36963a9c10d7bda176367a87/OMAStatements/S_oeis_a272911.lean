import Mathlib.Data.Nat.Fib.Basic

/-!
# Gaps between Lucas products (OEIS A272911)

Source: https://oeis.org/A272911/internal

The source indexes Lucas products from one, as its Mathematica enumeration
and initial gap do. Both indices of a gap product are positive. Allowing
zero indices for a proposed gap product would only widen the conclusion.
-/

namespace OMA.S_oeis_a272911

/-- Lucas numbers in their conventional zero-based recurrence. --/
def L : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n+2 => L n + L (n+1)

def Mem (x : ℤ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ 1 ≤ j ∧ x = L i * L j

def FProduct (x : ℤ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ 1 ≤ j ∧ x = (Nat.fib i : ℤ) * (Nat.fib j : ℤ)

def Consecutive (x y : ℤ) : Prop :=
  x < y ∧ Mem x ∧ Mem y ∧ ∀ z : ℤ, x < z → z < y → ¬ Mem z

theorem main : ∀ x y : ℤ, Consecutive x y → Mem (y-x) ∨ FProduct (y-x) := by
  sorry

end OMA.S_oeis_a272911
