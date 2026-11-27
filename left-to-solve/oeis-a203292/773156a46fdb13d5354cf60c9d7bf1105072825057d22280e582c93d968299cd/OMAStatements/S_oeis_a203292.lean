import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Balanced arrays of length four in A203292

Source: https://oeis.org/A203292
Credit: @eliayousf

Each tuple represents one array. Filtering tests weakly increasing order,
zero total sum, and equality of the two strict sign counts.
The formulas use the source offset `n ≥ 1`. The generating function starts
at index 1, so its coefficient at index zero is set to zero. Its denominator
has constant coefficient 1, so the displayed identity determines the series.
-/

namespace OMA.S_oeis_a203292

open Finset

abbrev Quad := ℤ × ℤ × ℤ × ℤ

def positiveCount (q : Quad) : ℕ :=
  (if 0 < q.1 then 1 else 0) + (if 0 < q.2.1 then 1 else 0) +
    (if 0 < q.2.2.1 then 1 else 0) + (if 0 < q.2.2.2 then 1 else 0)

def negativeCount (q : Quad) : ℕ :=
  (if q.1 < 0 then 1 else 0) + (if q.2.1 < 0 then 1 else 0) +
    (if q.2.2.1 < 0 then 1 else 0) + (if q.2.2.2 < 0 then 1 else 0)

def good (q : Quad) : Prop :=
  q.1 ≤ q.2.1 ∧ q.2.1 ≤ q.2.2.1 ∧ q.2.2.1 ≤ q.2.2.2 ∧
    q.1 + q.2.1 + q.2.2.1 + q.2.2.2 = 0 ∧ positiveCount q = negativeCount q

noncomputable def arrays (n : ℕ) : Finset Quad := by
  classical
  let interval := Icc (-(n : ℤ)) (n : ℤ)
  exact (interval ×ˢ (interval ×ˢ (interval ×ˢ interval))).filter good

noncomputable def a (n : ℕ) : ℕ := (arrays n).card

noncomputable def seriesCoeff (n : ℕ) : ℤ := if n = 0 then 0 else (a n : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 ≤ n → n % 2 = 0 → 24 * a n = 24 + 32*n + 6*n^2 + 4*n^3) ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 1 → 24 * a n = 30 + 32*n + 6*n^2 + 4*n^3) ∧
    (((1 - X)^4 * (1 + X) : ℤ⟦X⟧) * mk seriesCoeff =
      X * (3 - 3*X + 3*X^3 - X^4)) := by
  sorry

end OMA.S_oeis_a203292
