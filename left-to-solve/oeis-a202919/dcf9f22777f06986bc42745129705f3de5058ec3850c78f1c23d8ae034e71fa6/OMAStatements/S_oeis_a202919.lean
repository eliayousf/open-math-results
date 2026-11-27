import Mathlib.Data.Finset.Sigma
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A202919 arrays with increments at most three

Source: https://oeis.org/A202919
Credit: @eliayousf

The first row and first column are zero. The two horizontal increments
in each row are encoded by the quotient and remainder modulo four.
The two remaining coordinates are required to increase by at most three
at each vertical step. The list enumerator counts exactly the row tuples
satisfying these constraints. The count at index zero is set to zero for
the ordinary generating function, which starts at index one.
-/

namespace OMA.S_oeis_a202919

open Finset PowerSeries
open scoped PowerSeries

abbrev Row := Fin 16

def firstHeight (row : Row) : ℕ := row.val / 4

def secondHeight (row : Row) : ℕ := row.val / 4 + row.val % 4

def follows (old new : Row) : Prop :=
  firstHeight old ≤ firstHeight new ∧ firstHeight new ≤ firstHeight old + 3 ∧
  secondHeight old ≤ secondHeight new ∧ secondHeight new ≤ secondHeight old + 3

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
    (∀ n : ℕ, 10 < n → a n = 10*a (n-1)-45*a (n-2)+120*a (n-3)-210*a (n-4)+252*a (n-5)-
      210*a (n-6)+120*a (n-7)-45*a (n-8)+10*a (n-9)-a (n-10)) ∧
    (((1-X)^10 : ℤ⟦X⟧) * mk a = X*(1+35*X^2-36*X^3+30*X^4-10*X^5+X^6)) := by
  sorry

end OMA.S_oeis_a202919
