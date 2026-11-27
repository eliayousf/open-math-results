import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Arndt’s weighted consecutive-divisor generating function

Source: https://oeis.org/A069972
-/

namespace OMA.S_oeis_a069972

open Finset

def triangular (d : ℕ) : ℕ := d * (d + 1) / 2

/-- Sum of the positive integers d for which d and d+1 both divide 2n. -/
def a (n : ℕ) : ℕ :=
  ∑ d ∈ Icc 1 (2 * n), if d ∣ 2 * n ∧ d + 1 ∣ 2 * n then d else 0

/-- Coefficients of the locally finite sum of d times X to the d-th triangular
number divided by one minus that same power of X. Each summand is expanded
geometrically; no index d > n can contribute at degree n. -/
def lambert : PowerSeries ℕ :=
  PowerSeries.mk fun n => ∑ d ∈ Icc 1 n, if triangular d ∣ n then d else 0

theorem main : PowerSeries.mk a = lambert := by
  sorry

end OMA.S_oeis_a069972
