import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Kimberling's strict least-two subset claim (A053599)

Source: https://oeis.org/A053599/internal

A sorted nonempty subset has palindromic gaps exactly when reflection across
its endpoint midpoint preserves it. The strict inequality for the two least
elements means every member other than the minimum satisfies it.
-/

namespace OMA.S_oeis_a053599

open Finset

/-- A nonempty subset with palindromic consecutive differences is symmetric
under reflection in the midpoint of its minimum and maximum. -/
def pal (S : Finset ℕ) : Prop :=
  ∃ u ∈ S, ∃ v ∈ S, ∀ x ∈ S, u ≤ x ∧ x ≤ v ∧ u + v - x ∈ S

/-- For a subset with minimum m and maximum L, the least-two condition
means that every other member x satisfies L < m + x. -/
def raised (S : Finset ℕ) : Prop :=
  ∃ m ∈ S, ∃ L ∈ S, m < L ∧ ∀ x ∈ S, m ≤ x ∧ x ≤ L ∧ (m ≠ x → L < m + x)

noncomputable def aset (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Icc 1 N).powerset.filter pal

noncomputable def bset (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Icc 1 N).powerset.filter raised

noncomputable def a (N : ℕ) := (aset N).card
noncomputable def b (N : ℕ) := (bset N).card

theorem main : b 0 = 0 ∧ b 1 = 0 ∧ ∀ n : ℕ, b (n + 2) = a (n + 1) := by
  sorry

end OMA.S_oeis_a053599
