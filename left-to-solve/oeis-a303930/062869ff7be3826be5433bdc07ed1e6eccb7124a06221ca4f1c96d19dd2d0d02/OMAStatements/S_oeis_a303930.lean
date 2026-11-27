import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.PowerSeries.Basic

/-! This is the count of leaf-free edge subsets of the 2 by n grid up to
reflection across each axis. Each transfer choice marks the rung and the
boundaries mark the two horizontal edges. The Burnside average counts the
four possible symmetries. The denominator is the expansion of the three
factors in the source. The initial zero respects the source's offset one.
Source: https://oeis.org/A303930/internal
-/

open Finset Matrix PowerSeries

namespace OMA.S_oeis_a303930

def bit (j r : ℕ) : ℕ := j / 2^r % 2

/-- Each column permits or omits its rung, omitting vertex degree one. -/
def transfer : Matrix (Fin 4) (Fin 4) ℤ :=
  fun o i => ((univ.filter fun rung : Fin 2 =>
     (∀ r : Fin 2, bit o.val r.val + bit i.val r.val + rung.val ≠ 1)).card : ℤ)

def v : ℕ → Fin 4 → ℤ
  | 0 => ![1,0,0,0]
  | n+1 => transfer *ᵥ v n

/-- Labelled subgraphs from empty mask to empty mask. -/
def unrestricted (n : ℕ) : ℤ := v n 0

/-- Horizontal symmetry restricts the boundary mask to 0 or 3. -/
def symmetricState : ℕ → ℤ × ℤ
  | 0 => (1,0)
  | n+1 =>
    let s := symmetricState n
    (s.1+s.2,s.1+2*s.2)

def horizontal (n : ℕ) : ℤ := (symmetricState n).1

/-- The total fixed-point count for the two reversals of column order.
For n even, the reflection and rotation weights are (1,1,1,1) and (1,0,0,1).
For n odd, their weights are the diagonal and swapped-diagonal entries. -/
def reflected (n : ℕ) : ℤ :=
  let s := v (n/2)
  if n%2=0 then 2*s 0+s 1+s 2+2*s 3 else 2*s 0+2*s 1+2*s 2+4*s 3

def numerator (n : ℕ) : ℤ := unrestricted n + horizontal n + reflected n

/-- Burnside average of the four grid symmetries. -/
def a (n : ℕ) : ℚ := (numerator n : ℚ)/4

/-- The source series starts at one. -/
def series (n : ℕ) : ℚ := if n=0 then 0 else a n

theorem main :
    (∀ n : ℕ, 9 ≤ n → a n = 8 * a (n-1) - 16 * a (n-2) - 20 * a (n-3) + 95 * a (n-4) - 60 * a (n-5) - 80 * a (n-6) + 100 * a (n-7) - 25 * a (n-8)) ∧
    ((1 - C 8 * X ^ 1 + C 16 * X ^ 2 + C 20 * X ^ 3 - C 95 * X ^ 4 +
      C 60 * X ^ 5 + C 80 * X ^ 6 - C 100 * X ^ 7 + C 25 * X ^ 8 : ℚ⟦X⟧) * mk series =
      X ^ 1 - C 6 * X ^ 2 + C 4 * X ^ 3 + C 30 * X ^ 4 - C 45 * X ^ 5 -
        C 22 * X ^ 6 + C 60 * X ^ 7 - C 20 * X ^ 8) := by
  sorry

end OMA.S_oeis_a303930
