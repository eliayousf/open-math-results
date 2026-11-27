import Mathlib.Data.Finset.Prod
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A202730 ascent-sequence arrays with three columns

Source: https://oeis.org/A202730
Credit: @eliayousf

The rows are triples of nonnegative integers. The five row types listed
below exhaust the three-entry ascent sequences. The column test tracks
the number of ascents in the prefix and compares the lower-right entry
with `min n 3 - 1`. The empty array has no lower-right entry and does not
contribute to the generating series. The denominator has constant term 1.
-/

namespace OMA.S_oeis_a202730

open Finset

abbrev Row := ℕ × ℕ × ℕ

def follows (previous ascents : ℕ) : List ℕ → Bool
  | [] => true
  | x :: xs => decide (x ≤ ascents + 1) &&
    follows x (ascents + if previous < x then 1 else 0) xs

/-- An ascent sequence starts at zero, and subsequent entries are bounded by
one plus the number of ascents in the preceding prefix. -/
def isAscent : List ℕ → Bool
  | [] => true
  | x :: xs => decide (x = 0) && follows x 0 xs

def rows : Finset Row := {(0,0,0), (0,0,1), (0,1,0), (0,1,1), (0,1,2)}

def prepend : (Row × List Row) ↪ List Row :=
  ⟨fun p => p.1 :: p.2, by
    rintro ⟨r,l⟩ ⟨s,k⟩ h
    simpa only [Prod.mk.injEq, List.cons.injEq] using h⟩

def words : ℕ → Finset (List Row)
  | 0 => {[]}
  | n + 1 => (rows ×ˢ words n).map prepend

def condition (n : ℕ) (l : List Row) : Bool :=
  isAscent (l.map (fun r => r.1)) && isAscent (l.map (fun r => r.2.1)) &&
    isAscent (l.map (fun r => r.2.2)) &&
    decide (l.getLast?.map (fun r => r.2.2) = some (min n 3 - 1))

def arrays (n : ℕ) : Finset (List Row) := (words n).filter (fun l => condition n l = true)

def a (n : ℕ) : ℕ := (arrays n).card

open PowerSeries in
theorem main :
    (∀ n : ℕ, 2 < n → (150 : ℤ) * a n = 4*(5 : ℤ)^n - 25*(2 : ℤ)^n) ∧
    (((1 - 2*X)*(1 - 5*X) : ℤ⟦X⟧) * mk (fun n => (a n : ℤ)) =
      X * (1 - 5*X - 2*X^2 + 20*X^3)) := by
  sorry

end OMA.S_oeis_a202730
