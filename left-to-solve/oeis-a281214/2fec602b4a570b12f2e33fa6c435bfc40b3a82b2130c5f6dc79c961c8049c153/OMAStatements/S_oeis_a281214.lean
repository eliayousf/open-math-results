import Mathlib

/-!
# OEIS A281214: Barker's conjectures for the left x-axis of the two-dimensional Rule 342 in binary

Source: https://oeis.org/A281214 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A281214 (Robert Price, Jan 17 2017), offset 0: Binary representation of the x-axis, from the
left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 342, based on the 5-celled von Neumann neighborhood. Comment: Initialized with a
single black (ON) cell at stage zero.
Formula section:
Conjectures from Colin Barker, Jan 18 2017:
a(n) = 100*a(n-2) + a(n-4) - 100*a(n-6) for n>5.
G.f.: (1 + 11*x + 10*x^3) / ((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)*(1 + x^2)).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell (Rule 342 keeps an OFF cell with no ON neighbor OFF,
  so the background stays OFF). The entry's program runs on a finite torus of side 2*128+1, which
  agrees with the plane for the stages listed.
* Counting convention: as the name and the program say (FromDigits in base 10 of the middle row
  from the left edge to the center), a(n) writes the cells (-n,0), ..., (0,0) of stage n as
  binary digits, the left edge first, and reads them in base 10.
* The statement is the conjunction of both conjectures. The recurrence is stated in the integers,
  and the generating function A(x) = Sum_{n >= 0} a(n) x^n = N/D is stated as A * D = N in the
  formal power series ring over the integers, which is equivalent because D has constant term 1.
* Controls from the entry, proved in the proof file: a(0..9) = 1, 11, 100, 1110, 10001, 111011,
  1000100, 11101110, 100010001, 1110111011.
-/

namespace OMA.S_oeis_a281214

open PowerSeries

/-- Stage t of the two-dimensional Rule 342 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 342 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- A281214(n): the cells (-n,0), ..., (0,0) of stage n as decimal digits, left edge first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n (-(k : ℤ)) 0 then 10 ^ k else 0

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 100 * a (n - 2) + a (n - 4) - 100 * a (n - 6)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + X ^ 2)) =
      1 + 11 * X + 10 * X ^ 3 := by
  sorry

end OMA.S_oeis_a281214
