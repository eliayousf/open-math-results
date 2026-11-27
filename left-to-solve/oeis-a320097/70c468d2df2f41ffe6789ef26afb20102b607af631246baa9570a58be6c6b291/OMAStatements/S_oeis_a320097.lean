import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.PowerSeries.Basic

open Finset Matrix PowerSeries

/-! Literal transfer count for the no-leaf subgraphs of a fixed-width grid.
Left and right masks say which horizontal edges enter and leave a column.
The internal mask specifies its vertical edges. The degree check excludes
one at every vertex. Both exterior boundary masks are empty.
Source: https://oeis.org/A320097/internal
-/

namespace OMA.S_oeis_a320097

/-- Whether the edge at position r is chosen in the mask. -/
def bit (mask r : ℕ) : ℕ := mask / 2^r % 2

/-- Count admissible vertical edges inside the column with the two boundary masks. -/
def transfer : Matrix (Fin 16) (Fin 16) ℤ :=
  fun out inc => ((univ.filter fun inside : Fin 8 =>
    ∀ r : Fin 4, bit out.val r.val + bit inc.val r.val + bit inside.val r.val +
      (if 0 < r.val then bit inside.val (r.val-1) else 0) ≠ 1).card : ℤ)

/-- Count partial configurations for each mask of edges continuing to the right. -/
def state : ℕ → Fin 16 → ℤ
  | 0 => fun j => if j = 0 then 1 else 0
  | n + 1 => transfer *ᵥ state n

/-- Empty boundaries count exactly the no-leaf subgraphs of the 4 by n grid. -/
def a (n : ℕ) : ℤ := state n 0

/-- Use the published offset one in the generating function. -/
def series (n : ℕ) : ℤ := if n = 0 then 0 else a n

theorem main :
    (∀ n : ℕ, 7 ≤ n → a n = 36 * a (n - 1) - 7 * a (n - 2) - 201 * a (n - 3)
      + 49 * a (n - 4) + 20 * a (n - 5) - 5 * a (n - 6)) ∧
    ((1 - C 36 * X ^ 1 + C 7 * X ^ 2 + C 201 * X ^ 3 -
      C 49 * X ^ 4 - C 20 * X ^ 5 + C 5 * X ^ 6 : ℤ⟦X⟧) * mk series =
      X ^ 1 - C 21 * X ^ 2 - C 70 * X ^ 3 + C 10 * X ^ 4 + C 14 * X ^ 5 - C 3 * X ^ 6) := by
  sorry

end OMA.S_oeis_a320097
