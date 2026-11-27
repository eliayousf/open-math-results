import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Distance-bounded arrays of width three

Source: https://oeis.org/A252815
Replace each cell by its distance from the upper left minus its value.
The resulting entries are in 0..2, start at zero at the upper left, and
each horizontal and vertical step still increases by zero or one. This
replacement is reversible. The eight admissible row states are listed
explicitly, the first four can be initial rows, and the matrix counts
their allowed vertical transitions. The source begins at n=1.
-/

namespace OMA.S_oeis_a252815

open Finset Matrix PowerSeries
open scoped PowerSeries

abbrev Row := Fin 8

def rowHeights : Row → ℕ × ℕ × ℕ :=
  ![(0,0,0), (0,0,1), (0,1,1), (0,1,2), (1,1,1), (1,1,2), (1,2,2), (2,2,2)]

def firstHeight (row : Row) : ℕ := (rowHeights row).1

def secondHeight (row : Row) : ℕ := (rowHeights row).2.1

def thirdHeight (row : Row) : ℕ := (rowHeights row).2.2

def firstRow (i : Fin 4) : Row := ⟨i.val, by have := i.isLt; omega⟩

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
  | n + 1 => ∑ i : Fin 4, ∑ row : Row, (transition ^ n) (firstRow i) row

theorem main :
    (((1-X)^7 : ℤ⟦X⟧) * mk a = X*(4-11*X+28*X^2-37*X^3+27*X^4-11*X^5+2*X^6)) ∧
    (∀ n : ℕ, 7 < n →
      a n = 7*a (n-1)-21*a (n-2)+35*a (n-3)-35*a (n-4)+21*a (n-5)-7*a (n-6)+a (n-7)) := by
  sorry

end OMA.S_oeis_a252815
