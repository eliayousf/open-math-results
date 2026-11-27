import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Binary-increment arrays of width four

Source: https://oeis.org/A202752
A row stores the three horizontal increments in its binary digits. Its entries
are zero and the three prefix sums of those digits. A matrix entry is 1 exactly
when each nontrivial vertical difference is zero or one. For n ≥ 1 the row sum
of the (n−1)st power from the zero state counts the original arrays.
-/

namespace OMA.S_oeis_a202752

open Finset Matrix PowerSeries
open scoped PowerSeries

abbrev Row := Fin 8

def firstHeight (row : Row) : ℕ := row.val / 4

def secondHeight (row : Row) : ℕ := row.val / 4 + (row.val / 2) % 2

def thirdHeight (row : Row) : ℕ := secondHeight row + row.val % 2

def follows (old new : Row) : Prop :=
  firstHeight old ≤ firstHeight new ∧ firstHeight new ≤ firstHeight old + 1 ∧
  secondHeight old ≤ secondHeight new ∧ secondHeight new ≤ secondHeight old + 1 ∧
  thirdHeight old ≤ thirdHeight new ∧ thirdHeight new ≤ thirdHeight old + 1

instance (old new : Row) : Decidable (follows old new) := by
  unfold follows
  infer_instance

def transition : Matrix Row Row ℤ := fun old new => if follows old new then 1 else 0

def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => ∑ row : Row, (transition ^ n) 0 row

theorem main :
    (((1-X)^7 : ℤ⟦X⟧) * mk a = X*(1-3*X+10*X^2-8*X^3+2*X^4)) ∧
    (∀ n : ℕ, 7 < n →
      a n = 7*a (n-1)-21*a (n-2)+35*a (n-3)-35*a (n-4)+21*a (n-5)-7*a (n-6)+a (n-7)) := by
  sorry

end OMA.S_oeis_a202752
