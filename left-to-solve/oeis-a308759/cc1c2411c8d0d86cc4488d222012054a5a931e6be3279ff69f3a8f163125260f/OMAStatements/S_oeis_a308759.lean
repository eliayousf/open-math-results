import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A308759: sum of the second-largest parts of four-part partitions

Source: https://oeis.org/A308759
The sorted parts are (1+p,1+p+q,1+p+q+r,1+p+q+r+s), with nonnegative gaps.
The sum of the parts is 4+4p+3q+2r+s, and their second-largest part is
1+p+q+r. The terms below sum its constant, p, q and r contributions.
-/

namespace OMA.S_oeis_a308759

def accumulate (d : ℕ) (f : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (m/d+1), f (m-d*i)

def weighted (d : ℕ) (f : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (m/d+1), (i : ℤ) * f (m-d*i)

def ones : ℕ → ℤ := fun _ ↦ 1
def pairs : ℕ → ℤ := accumulate 2 ones
def triples : ℕ → ℤ := accumulate 3 pairs
def partCount : ℕ → ℤ := accumulate 4 triples
def pWeight : ℕ → ℤ := weighted 4 triples
def qWeight : ℕ → ℤ := accumulate 4 (weighted 3 pairs)

def rWeight : ℕ → ℤ := accumulate 4 (accumulate 3 (weighted 2 ones))

def a (n : ℕ) : ℤ := if 4 ≤ n then partCount (n-4) + pWeight (n-4) + qWeight (n-4) + rWeight (n-4) else 0

theorem main :
    (let x := (PowerSeries.X : PowerSeries ℤ)
     ((1-x)^5*(1+x)^3*(1+x^2)^2*(1+x+x^2)^2) * PowerSeries.mk a =
        x^4*(1+x+2*x^2+2*x^3+3*x^4+2*x^5+2*x^6)) ∧
    (∀ n : ℕ, 15 < n →
      a n = a (n-2) + 2*a (n-3) + 2*a (n-4) - 2*a (n-5) - 3*a (n-6) - 4*a (n-7)
        + 4*a (n-9) + 3*a (n-10) + 2*a (n-11) - 2*a (n-12) - 2*a (n-13)
        - a (n-14) + a (n-16)) := by
  sorry

end OMA.S_oeis_a308759
