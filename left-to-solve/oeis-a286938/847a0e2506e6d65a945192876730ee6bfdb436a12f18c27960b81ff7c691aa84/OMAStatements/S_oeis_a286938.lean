import Mathlib.Data.Int.Basic

/-! The conjectured A286938 recurrence for the lengths of the iterated word.
Source: https://oeis.org/A286938/internal
The Mathematica rule applies nonoverlapping replacements from left to right.
The recurrence starts at the first index with five preceding terms. -/

namespace OMA.S_oeis_a286938

/-- Nonoverlapping left-to-right replacement of 00 by 001 and 1 by 10. -/
def rewriteWord : List Bool → List Bool
  | [] => []
  | true :: xs => true :: false :: rewriteWord xs
  | false :: false :: xs => false :: false :: true :: rewriteWord xs
  | false :: xs => false :: rewriteWord xs

def word : ℕ → List Bool
  | 0 => [false,false]
  | n + 1 => rewriteWord (word n)

def a (n : ℕ) : ℕ := (word n).length

theorem main : ∀ n : ℕ, 5 ≤ n →
    (a n : ℤ) = 2 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ) + 2 * (a (n - 3) : ℤ) -
      3 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ) := by
  sorry

end OMA.S_oeis_a286938
