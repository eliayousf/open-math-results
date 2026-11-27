import Mathlib.Data.Finset.Sigma
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A202808 arrays of width four with increments at most two

Source: https://oeis.org/A202808
Credit: @eliayousf

The first row and column are zero. The three digits of a base-three row
index encode the horizontal increments `u`, `v`, `w`, so the actual row is
`(0, u, u + v, u + v + w)`. The three nonconstant column entries must each
increase by an amount in `0..2` at every vertical step. `gridFrom` enumerates
these row lists after the fixed initial zero row. The source sequence starts at
index one, so the generating function's constant coefficient is zero.
-/

namespace OMA.S_oeis_a202808

open Finset PowerSeries
open scoped PowerSeries

abbrev Row := Fin 27

def firstHeight (row : Row) : ℕ := row.val / 9

def secondHeight (row : Row) : ℕ := firstHeight row + row.val / 3 % 3

def thirdHeight (row : Row) : ℕ := secondHeight row + row.val % 3

def follows (old new : Row) : Prop :=
  firstHeight old ≤ firstHeight new ∧ firstHeight new ≤ firstHeight old + 2 ∧
  secondHeight old ≤ secondHeight new ∧ secondHeight new ≤ secondHeight old + 2 ∧
  thirdHeight old ≤ thirdHeight new ∧ thirdHeight new ≤ thirdHeight old + 2

instance (old new : Row) : Decidable (follows old new) := by
  unfold follows
  infer_instance

def prepend : (Σ _ : Row, List Row) ↪ List Row :=
  ⟨fun p => p.1 :: p.2, by
    rintro ⟨r,l⟩ ⟨s,k⟩ h
    change r :: l = s :: k at h
    obtain ⟨rfl,rfl⟩ := List.cons.inj h
    rfl⟩

/-- The lists of successive rows that can be appended to the current row. -/
def gridFrom : ℕ → Row → Finset (List Row)
  | 0, _ => {[]}
  | n + 1, row => ((Finset.univ.filter (follows row)).sigma (gridFrom n)).map prepend

def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => (gridFrom n 0).card

theorem main :
    (∀ n : ℕ, 13 < n → a n = 13*a (n-1) - 78*a (n-2) + 286*a (n-3) - 715*a (n-4) + 1287*a (n-5)
      - 1716*a (n-6) + 1716*a (n-7) - 1287*a (n-8) + 715*a (n-9)
      - 286*a (n-10) + 78*a (n-11) - 13*a (n-12) + a (n-13)) ∧
    (((1-X)^13 : ℤ⟦X⟧) * mk a = X * (1 - 3*X + 69*X^2 + 98*X^3 + 224*X^4 - 470*X^5 +
      607*X^6 - 459*X^7 + 228*X^8 - 71*X^9 + 13*X^10 - X^11)) := by
  sorry

end OMA.S_oeis_a202808
