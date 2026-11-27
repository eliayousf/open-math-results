import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Infinitude of the distinct-repdigit sequence A336759

Source: https://oeis.org/A336759
Every positive index asks for a representable integer whose minimum
number of distinct repdigit summands is at least that index.
-/

namespace OMA.S_oeis_a336759

open Finset

def repunit : ℕ → ℕ
  | 0 => 0
  | l+1 => 10 * repunit l + 1

/-- Positive decimal numbers consisting of a single nonzero repeated digit. -/
def IsRepdigit (m : ℕ) : Prop :=
  ∃ d l : ℕ, 1 ≤ d ∧ d ≤ 9 ∧ 1 ≤ l ∧ m = d * repunit l

/-- A representation by a finite set of distinct decimal repdigits. -/
def Decomposition (m : ℕ) (s : Finset ℕ) : Prop :=
  (∀ d ∈ s, IsRepdigit d) ∧ ∑ d ∈ s, d = m

theorem main : ∀ n ≥ 1,
    ∃ m : ℕ, 0 < m ∧ (∃ s : Finset ℕ, Decomposition m s) ∧
      ∀ s : Finset ℕ, Decomposition m s → n ≤ s.card := by
  sorry

end OMA.S_oeis_a336759
