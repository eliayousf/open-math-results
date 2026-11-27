import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The prime-sum generating function conjecture of OEIS A034387

Source: https://oeis.org/A034387
For each degree n, the triple sum has finitely many contributing pairs
1 ≤ i ≤ j ≤ n. Its primality condition i-j+n is written i+n-j to avoid
truncating a subtraction before adding n.
-/

namespace OMA.S_oeis_a034387

def primeSum (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.Icc 1 n, if p.Prime then p else 0

def tripleCoeff (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc i n, if (i+n-j).Prime then 1 else 0

theorem main : PowerSeries.mk primeSum = PowerSeries.mk tripleCoeff := by
  sorry

end OMA.S_oeis_a034387
