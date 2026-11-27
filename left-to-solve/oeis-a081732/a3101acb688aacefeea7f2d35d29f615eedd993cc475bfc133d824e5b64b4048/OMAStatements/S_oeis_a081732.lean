import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Digits.Lemmas

/-! Zhuorui He's nine ternary neighbour-count recurrences.
Source: https://oeis.org/A081732/internal
The lower digit is first in the stored words. The three edit classes
are disjoint by resulting length, and only canonical numeral strings
are counted. The variables d and e range over all three trits. -/

namespace OMA.S_oeis_a081732

open Finset

abbrev Digit := Fin 3
abbrev Word := List Digit

def pref (d : Digit) : Word ↪ Word :=
  ⟨List.cons d, fun _ _ h => (List.cons.inj h).2⟩

def firstDigit (s : Word) : Digit ↪ Word :=
  ⟨fun d => d :: s, fun _ _ h => (List.cons.inj h).1⟩

def deletions : Word → Finset Word
  | [] => ∅
  | d :: s => insert s ((deletions s).map (pref d))

def insertions : Word → Finset Word
  | [] => univ.map (firstDigit [])
  | d :: s => (univ.map (firstDigit (d :: s))) ∪ ((insertions s).map (pref d))

def substitutions : Word → Finset Word
  | [] => ∅
  | d :: s => ((univ.erase d).map (firstDigit s)) ∪ ((substitutions s).map (pref d))

/-- Least significant digit first. A singleton zero denotes zero. -/
def canonical (s : Word) : Prop :=
  s ≠ [] ∧ (s.length = 1 ∨ s.getLast? ≠ some 0)

instance : DecidablePred canonical := fun _ => by unfold canonical; infer_instance

/-- The three edit classes have distinct lengths and each contains canonical words. -/
def count (s : Word) : ℕ :=
  ((deletions s).filter canonical).card + ((insertions s).filter canonical).card +
  ((substitutions s).filter canonical).card

def trit (x : ℕ) : Digit := ⟨x % 3, Nat.mod_lt _ (by decide)⟩

def numeral (n : ℕ) : Word := if n = 0 then [0] else (Nat.digits 3 n).map trit

def a (n : ℕ) : ℕ := count (numeral n)

theorem main : ∀ m : ℕ, 3 ≤ m → ∀ d e : Digit,
    a (9*m + 3*(d:ℕ) + (e:ℕ)) =
      a (3*m + (d:ℕ)) + if d = e then 4 else 5 := by
  sorry

end OMA.S_oeis_a081732
