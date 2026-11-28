import Mathlib

/-!
# OEIS A284481

Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of
growth of the two-dimensional cellular automaton defined by Rule 950, based on the 5-celled von
Neumann neighborhood.

Source: https://oeis.org/A284481
Conjectures: Colin Barker, Mar 28 2017.
Formalization: @longling12 (drafted with AI assistance)

Initially only the origin is ON. On the whole integer plane, bit c+2s of the rule gives the
next state, where c is the central bit and s counts the four orthogonal ON neighbors.
The central row runs from left edge to origin inclusive. Its first cell is the most significant
digit in base 2.
The sequence starts at n = 0. Generating functions are ordinary formal power series.
-/

namespace OMA.S_oeis_a284481

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

def a (n : ℕ) : ℤ := digits 950 n

theorem main :
    (PowerSeries.mk a * ((1 - X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2)) =
      1 + 2 * X + 2 * X ^ 2 + 10 * X ^ 3 - 8 * X ^ 4 + 8 * X ^ 5 - 16 * X ^ 7 + 16 * X ^ 8) ∧
    (∀ n : ℕ, 5 < n → a n = a (n - 1) + 16 * a (n - 4) - 16 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a284481
