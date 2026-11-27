import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Bounded-increment arrays of width three

Source: https://oeis.org/A202807
A row stores the two horizontal increments as its base-three digits. Its
actual entries are 0, the first digit, and the sum of the two digits. The
matrix entry is 1 exactly when both vertical differences are in 0..2. Thus
the row sum of the (n−1)st power from the zero row counts the original
n-row arrays. The generating function starts at n=1 as in the source.
-/

namespace OMA.S_oeis_a202807

open Finset Matrix PowerSeries
open scoped PowerSeries

abbrev Row := Fin 9

def firstHeight (row : Row) : ℕ := row.val / 3

def secondHeight (row : Row) : ℕ := row.val / 3 + row.val % 3

def follows (old new : Row) : Prop :=
  firstHeight old ≤ firstHeight new ∧ firstHeight new ≤ firstHeight old + 2 ∧
  secondHeight old ≤ secondHeight new ∧ secondHeight new ≤ secondHeight old + 2

instance (old new : Row) : Decidable (follows old new) := by
  unfold follows
  infer_instance

def transition : Matrix Row Row ℤ := fun old new => if follows old new then 1 else 0

def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => ∑ row : Row, (transition ^ n) 0 row

theorem main :
    (((1-X)^7 : ℤ⟦X⟧) * mk a = X*(1-X+11*X^2-12*X^3+6*X^4-X^5)) ∧
    (∀ n : ℕ, 7 < n →
      a n = 7*a (n-1)-21*a (n-2)+35*a (n-3)-35*a (n-4)+21*a (n-5)-7*a (n-6)+a (n-7)) := by
  sorry

end OMA.S_oeis_a202807
