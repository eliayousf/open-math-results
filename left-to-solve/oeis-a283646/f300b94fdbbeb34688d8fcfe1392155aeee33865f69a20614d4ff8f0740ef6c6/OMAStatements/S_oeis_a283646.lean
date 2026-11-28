import Mathlib

/-!
# OEIS A283646

Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of
growth of the two-dimensional cellular automaton defined by Rule 694, based on the 5-celled von
Neumann neighborhood.

Source: https://oeis.org/A283646
Conjectures: Colin Barker, Mar 14 2017.
Formalization: @longling12 (drafted with AI assistance)

Initially only the origin is ON. On the whole integer plane, bit c+2s of the rule gives the
next state, where c is the central bit and s counts the four orthogonal ON neighbors.
The central row runs from left edge to origin inclusive. Its first cell is the most significant
digit in base 2.
The sequence starts at n = 0. Generating functions are ordinary formal power series.
-/

namespace OMA.S_oeis_a283646

open PowerSeries

/-- Synchronous evolution on the integer plane from one ON cell. -/
def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t+1, x, y =>
    let s := state r t
    r.testBit ((s x y).toNat + 2 * ((s (x-1) y).toNat + (s (x+1) y).toNat +
      (s x (y-1)).toNat + (s x (y+1)).toNat))

/-- Read the central row from left edge to origin, most significant digit first. -/
def digits (r n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n+1), ((state r n ((i : ℤ) - n) 0).toNat : ℤ) * 2 ^ (n-i)

def a (n : ℕ) : ℤ := digits 694 n

theorem main :
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) * (1 + 16 * X ^ 4))
      =
      1 + 3 * X + 4 * X ^ 2 + 10 * X ^ 3 + 16 * X ^ 4 + 40 * X ^ 5 + 72 * X ^ 6 + 152 * X ^ 7 - 128 * X
      ^ 9 + 128 * X ^ 10 - 128 * X ^ 11 + 256 * X ^ 15) ∧
    (∀ n : ℕ, 11 < n → a n = a (n - 2) + 256 * a (n - 8) - 256 * a (n - 10)) := by
  sorry

end OMA.S_oeis_a283646
