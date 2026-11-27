import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Dist

/-! The two endpoint counts in Dawid Ryłko's conjecture for OEIS A401673.

A domicule tiling of the 2n by 2n board is a fixed-point-free involution of
its labelled cells, with row and column displacements at most one. Diagonal
pieces have both displacements one and may cross, as the source specifies.
These counts describe T(n,n^2) and T(n,n^2-1) through cell pairings.
The first counts all-diagonal pairings. The second counts configurations with
four ordinary endpoints, equivalently exactly two ordinary pieces.
The second coefficient is defined only for n at least one.
Source: https://oeis.org/A401673/internal
-/

namespace OMA.S_oeis_a401673

open Finset

abbrev Cell (n : ℕ) := Fin (2 * n) × Fin (2 * n)

/-- A fully diagonal tiling, as the involution pairing each cell to its mate. -/
abbrev AllDiagonal (n : ℕ) :=
  {mate : Cell n → Cell n // Function.Involutive mate ∧
    ∀ u, Nat.dist (mate u).1.val u.1.val = 1 ∧ Nat.dist (mate u).2.val u.2.val = 1}

noncomputable def diagonalCount (n : ℕ) : ℕ :=
  letI : Fintype (AllDiagonal n) := Fintype.ofFinite _
  Fintype.card (AllDiagonal n)

def isHorizontal {n : ℕ} (mate : Cell n → Cell n) (u : Cell n) : Prop :=
  (mate u).1 = u.1

def isVertical {n : ℕ} (mate : Cell n → Cell n) (u : Cell n) : Prop :=
  (mate u).2 = u.2

instance {n : ℕ} (mate : Cell n → Cell n) : DecidablePred (isHorizontal mate) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

instance {n : ℕ} (mate : Cell n → Cell n) : DecidablePred (isVertical mate) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

def ordinaryCells {n : ℕ} (mate : Cell n → Cell n) : Finset (Cell n) :=
  univ.filter fun v => isHorizontal mate v ∨ isVertical mate v

abbrev TwoOrdinary (n : ℕ) :=
  {m : Cell n → Cell n // Function.Involutive m ∧ (∀ u, m u ≠ u) ∧
    (∀ u, Nat.dist (m u).1.val u.1.val ≤ 1) ∧
    (∀ u, Nat.dist (m u).2.val u.2.val ≤ 1) ∧ (ordinaryCells m).card = 4}

noncomputable def nearCount (n : ℕ) : ℕ :=
  letI : Fintype (TwoOrdinary n) := Fintype.ofFinite _
  Fintype.card (TwoOrdinary n)

theorem main :
    (∀ n : ℕ, diagonalCount n = 1) ∧
    (∀ n : ℕ, 1 ≤ n → nearCount n = n ^ 2 * (n + 1)) := by
  sorry

end OMA.S_oeis_a401673
