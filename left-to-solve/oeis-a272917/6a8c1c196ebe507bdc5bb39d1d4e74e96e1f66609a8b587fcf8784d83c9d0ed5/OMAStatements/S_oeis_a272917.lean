import Mathlib.Data.Nat.Fib.Basic

/-!
# Gaps in the union of Fibonacci and Lucas products (A272917)

Source: https://oeis.org/A272917/internal

The positive-index Lucas sequence and the positive Fibonacci sequence
give the two sets of products in A272916.
-/

namespace OMA.S_oeis_a272917

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

def Both (x : ℤ) : Prop := Mem x ∨ FProduct x

def ConsecutiveBoth (x y : ℤ) : Prop :=
  x<y ∧ Both x ∧ Both y ∧ ∀ z : ℤ, x<z → z<y → ¬Both z

theorem main : ∀ x y : ℤ, ConsecutiveBoth x y → Both (y-x) := by
  sorry

end OMA.S_oeis_a272917
