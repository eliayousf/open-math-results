import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Linarith

/-!
# Arndt’s square-minus-triangular generating function

Source: https://oeis.org/A078703
-/

namespace OMA.S_oeis_a078703

open Finset

/-- Positive square roots x and nonnegative triangular indices k giving
a representation of n as x squared minus k times k plus one. -/
def squareWays (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 n) ×ˢ (range n)).filter (fun p => p.1 ^ 2 = n + p.2 * (p.2 + 1))

def a (n : ℕ) : ℕ := (squareWays n).card

/-- The coefficient support of the locally finite sum
of X to the j-th square divided by one minus X to the power 2j−1. -/
def rows (n : ℕ) : Finset ℕ :=
  (Icc 1 n).filter (fun j => j ^ 2 ≤ n ∧ (2 * j - 1) ∣ n - j ^ 2)

def lambert : PowerSeries ℕ := PowerSeries.mk (fun n => (rows n).card)

theorem main : PowerSeries.mk a = lambert := by
  sorry

end OMA.S_oeis_a078703
