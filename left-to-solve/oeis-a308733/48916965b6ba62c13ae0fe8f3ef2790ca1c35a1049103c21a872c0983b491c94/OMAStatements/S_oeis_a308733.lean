import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A308733: sum of the smallest parts of four-part partitions

Source: https://oeis.org/A308733
The successive differences of a partition with parts in nondecreasing order
give nonnegative gaps p,q,r,s by (a,b,c,d) = (1+p,1+p+q,1+p+q+r,1+p+q+r+s).
Their sum is 4+4p+3q+2r+s and their weight is 1+p. With p and q fixed, the
number of possible r,s is floor((n-4-4p-3q)/2)+1.
-/

namespace OMA.S_oeis_a308733

def pairs (m : ℕ) : ℤ := (m / 2 : ℕ) + 1

def triples (m : ℕ) : ℤ :=
  ∑ q ∈ Finset.range (m / 3 + 1), pairs (m-3*q)

def weight (m : ℕ) : ℤ :=
  ∑ p ∈ Finset.range (m / 4 + 1), ((p : ℤ)+1) * triples (m-4*p)

def a (n : ℕ) : ℤ := if 4 ≤ n then weight (n-4) else 0

theorem main :
    (let x := (PowerSeries.X : PowerSeries ℤ)
     ((1-x)^5*(1+x)^3*(1+x^2)^2*(1+x+x^2)) * PowerSeries.mk a = x^4) ∧
    (∀ n : ℕ, 13 < n →
      a n = a (n-1) + a (n-2) + a (n-4) - 3*a (n-5) - a (n-6) + a (n-8)
        + 3*a (n-9) - a (n-10) - a (n-12) - a (n-13) + a (n-14)) := by
  sorry

end OMA.S_oeis_a308733
