import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

open Finset Matrix

/-! Literal transfer count for the no-leaf subgraphs of a fixed-width grid.
Left and right masks say which horizontal edges enter and leave a column.
The internal mask specifies its vertical edges. The degree check excludes
one at every vertex. Both exterior boundary masks are empty.
Source: https://oeis.org/A320099/internal
-/

namespace OMA.S_oeis_a320099

/-- Whether the edge at position r is chosen in the mask. -/
def bit (mask r : ℕ) : ℕ := mask / 2^r % 2

/-- Count admissible vertical edges inside the column with the two boundary masks. -/
def transfer : Matrix (Fin 32) (Fin 32) ℤ :=
  fun out inc => ((univ.filter fun inside : Fin 16 =>
    ∀ r : Fin 5, bit out.val r.val + bit inc.val r.val + bit inside.val r.val +
      (if 0 < r.val then bit inside.val (r.val-1) else 0) ≠ 1).card : ℤ)

/-- Count partial configurations for each mask of edges continuing to the right. -/
def state : ℕ → Fin 32 → ℤ
  | 0 => fun j => if j = 0 then 1 else 0
  | n + 1 => transfer *ᵥ state n

/-- Empty boundaries count exactly the no-leaf subgraphs of the 5 by n grid. -/
def a (n : ℕ) : ℤ := state n 0

theorem main :
    (∀ n : ℕ, 11 ≤ n → a n = 103 * a (n - 1) + 1063 * a (n - 2) - 1873 * a (n - 3)
      - 20274 * a (n - 4) + 44071 * a (n - 5) - 10365 * a (n - 6)
      - 20208 * a (n - 7) + 5959 * a (n - 8) + 2300 * a (n - 9)
      - 500 * a (n - 10)) := by
  sorry

end OMA.S_oeis_a320099
