import Mathlib

/-!
Source: https://oeis.org/A081673
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A081/A081673.seq
Credit: @sntntHb

A081673: Expansion of exp(3x) - exp(x)(1-BesselI_0(2x)).

Source text: Conjecture: n(2n - 7)a(n) +(-12n^2 + 50n - 33)a(n-1)
+(16n^2 - 76n + 87)a(n-2) +3(4n^2 - 22n + 27)a(n-3) -9(2n-5)(n-3)a(n-4)=0
(R. J. Mathar). Robert Israel (Jun 03 2016) gives a differential equation for
the e.g.f. which implies the recursion.

Expanding the e.g.f.: exp(3x) has coefficient 3^n and exp(x) has coefficient 1;
BesselI_0(2x) = Sum_j x^(2j)/(j!)^2 has e.g.f. coefficient C(2j,j) at 2j, so
exp(x)BesselI_0(2x) has coefficient Sum_j C(n,2j) C(2j,j) (the central
trinomial coefficients). Hence a(n) = 3^n - 1 + Sum_j C(n,2j) C(2j,j)
(first terms 1, 3, 11, 33, 99, 293, 869, as in the OEIS data).

Formalized: Mathar's recursion on its full domain n>=4 (offset 0; checked
numerically for 4 <= n < 80).
-/

namespace OMA.S_oeis_a081673

def a (n : ℕ) : ℤ :=
  (3:ℤ)^n-1+∑ j ∈ Finset.range (n/2+1), (n.choose (2*j):ℤ)*((2*j).choose j:ℤ)

theorem main :
    ∀ n : ℕ, 4 ≤ n →
      (n:ℤ)*(2*(n:ℤ)-7)*a n+(-12*(n:ℤ)^2+50*(n:ℤ)-33)*a (n-1)
        +(16*(n:ℤ)^2-76*(n:ℤ)+87)*a (n-2)+3*(4*(n:ℤ)^2-22*(n:ℤ)+27)*a (n-3)
        -9*(2*(n:ℤ)-5)*((n:ℤ)-3)*a (n-4)=0 := by
  sorry

end OMA.S_oeis_a081673
