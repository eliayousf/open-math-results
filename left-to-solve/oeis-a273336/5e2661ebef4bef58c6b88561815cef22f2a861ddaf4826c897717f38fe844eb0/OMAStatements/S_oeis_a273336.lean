import Mathlib

/-!
# OEIS A273336: Barker's conjectures for the partial sums of the ON cells of the 2D Rule 657

Source: https://oeis.org/A273336 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A273336 (Robert Price, May 20 2016), offset 0: Partial sums of the number of active (ON,
black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 657,
based on the 5-celled von Neumann neighborhood. Comment: Initialized with a single black (ON)
cell at stage zero.
Formula section:
Conjectures from Colin Barker, May 20 2016:
a(n) = 2/3*(2*n^3+6*n^2+4*n-15) for n>1.
a(n) = 4*a(n-1)-6*a(n-2)+4*a(n-3)-a(n-4) for n>5.
G.f.: (1+x+8*x^2+8*x^3-17*x^4+7*x^5) / (1-x)^4.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule (Rule 657
  turns an OFF cell with no ON neighbor ON).
* Counting convention: stage t is counted in the square |x|, |y| <= t, which the entry's program
  keeps when it trims stage t to its central (2t+1) X (2t+1) square before counting, and a(n) is
  the sum of these counts over the stages 0, ..., n, as the program's running total; the listed
  terms are reproduced this way.
* The statement is the conjunction of the three conjectures: the closed form is stated in the
  rationals (so 2/3 is exact), the recurrence in the integers, and the generating function
  A(x) = Sum_{n >= 0} a(n) x^n = N/(1-x)^4 as A * (1-x)^4 = N in the formal power series ring
  over the integers.
* Controls from the entry, proved in the proof file: a(0..15) = 1, 5, 22, 70, 150, 270, 438, 662,
  950, 1310, 1750, 2278, 2902, 3630, 4470, 5430.
-/

namespace OMA.S_oeis_a273336

open PowerSeries

/-- Stage t of the two-dimensional Rule 657 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 657 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- The number of ON cells of stage t in the square |x|, |y| <= t. -/
noncomputable def count (t : ℕ) : ℕ :=
  ((Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t).filter
    (fun p => state t p.1 p.2 = true)).card

/-- A273336(n): the number of ON cells summed over the stages 0, ..., n. -/
noncomputable def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), count t

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 1 < n → (a n : ℚ) = 2 / 3 * (2 * n ^ 3 + 6 * n ^ 2 + 4 * n - 15)) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * (1 - X) ^ 4 =
      1 + X + 8 * X ^ 2 + 8 * X ^ 3 - 17 * X ^ 4 + 7 * X ^ 5 := by
  sorry

end OMA.S_oeis_a273336
