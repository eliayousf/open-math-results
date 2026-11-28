import Mathlib

/-!
# OEIS A285777: Barker's conjectures for the diagonal of the 2D Rule 89 from the corner, base 2

Source: https://oeis.org/A285777 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A285777 (Robert Price, Apr 25 2017), offset 0: Decimal representation of the diagonal from
the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 89, based on the 5-celled von Neumann neighborhood. Comment: Initialized with a
single black (ON) cell at stage zero.
Formula section:
Conjectures from Colin Barker, Apr 26 2017:
G.f.: (1 + 2*x - 4*x^2 + 4*x^3 - x^4 + x^5 + 4*x^6 - 4*x^7) / ((1 - x)*(1 + x)*(1 - 2*x)*(1 + 2*x)).
a(n) = 0 for n>3 and even.
a(n) = 2^(n+1) - 1 for n>3 and odd.
a(n) = 5*a(n-2) - 4*a(n-4) for n>7.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule (Rule 89
  turns an OFF cell with no ON neighbor ON). The entry's program runs on a finite torus of side
  2*128+1, which agrees with the plane for the stages listed.
* Counting convention: as the name says, a(n) writes the diagonal cells (n,n), ..., (1,1), (0,0)
  of stage n as binary digits, the corner first (most significant), and reads them in base 2.
  The listed terms are those of the diagonal. The entry's program reads the middle row
  (Range[i, 2*i-1] of the x-axis, in base 10) instead, which gives 0 rather than the listed 2 at
  n = 1; the definition follows the name and the data.
* The statement is the conjunction of the four conjectures. The generating function A(x) =
  Sum_{n >= 0} a(n) x^n = N/D is stated as A * D = N in the formal power series ring over the
  integers, which is equivalent because D has constant term 1; the odd closed form and the
  recurrence are stated in the integers.
* Controls from the entry, proved in the proof file: a(0..15) = 1, 2, 1, 14, 0, 63, 0, 255, 0,
  1023, 0, 4095, 0, 16383, 0, 65535.
-/

namespace OMA.S_oeis_a285777

open PowerSeries

/-- Stage t of the two-dimensional Rule 89 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 89 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- A285777(n): the cells (n,n), ..., (0,0) of stage n as binary digits, corner first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n (k : ℤ) (k : ℤ) then 2 ^ k else 0

/-- Barker's generating function, both closed forms and the recurrence. -/
theorem main :
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 + 2 * X - 4 * X ^ 2 + 4 * X ^ 3 - X ^ 4 + X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 ∧
    (∀ n : ℕ, 3 < n → Even n → a n = 0) ∧
    (∀ n : ℕ, 3 < n → Odd n → (a n : ℤ) = 2 ^ (n + 1) - 1) ∧
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a285777
