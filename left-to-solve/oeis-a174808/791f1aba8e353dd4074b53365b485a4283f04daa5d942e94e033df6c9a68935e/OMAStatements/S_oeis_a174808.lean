import Mathlib

/-!
# OEIS A174808: Mathar's D-finite recurrence for a transform of the large Schroeder numbers

Source: https://oeis.org/A174808 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Paul Barry, Mar 29 2010), offset 0: A transform of the large Schroeder numbers A006318.
Formulas: G.f.: (1-x-x^2-sqrt(1-6*x-5*x^2+2*x^3+x^4))/(2*x*(1+x)). a(n) =
Sum_{k=0..n} C(k,n-k)*A006318(k). Data: 1, 2, 8, 34, 162, 820, 4338, ... Formula: Conjecture:
(n+1)*a(n) +(-5*n+4)*a(n-1) +(-11*n+13)*a(n-2) +3*(-n+1)*a(n-3) +3*(n-4)*a(n-4) +(n-5)*a(n-5)=0.
- R. J. Mathar, Feb 10 2015

Formalization notes:
* The name is made precise by the entry's formula a(n) = Sum_{k=0..n} C(k,n-k)*A006318(k), which
  is also the entry's Maple program, and `a` formalizes it. A006318(k) is Mathlib's
  `Nat.largeSchroder k` (L(0) = 1, L(n+1) = L(n) + Sum_{i=0..n} L(i) L(n-i); 1, 2, 6, 22, 90, ...).
  C(k, n-k) is `Nat.choose`, which is 0 when n - k > k.
* `main` states the recurrence, in the integers, for every n >= 5: the range in which a(n), ...,
  a(n-5) are all terms of the sequence (offset 0), so every natural subtraction n - j is exact.
* Controls proved in the proof file: a(0..5) = 1, 2, 8, 34, 162, 820 as in the entry's data.
-/

namespace OMA.S_oeis_a174808

/-- A174808: a(n) = Sum_{k=0..n} C(k, n-k) A006318(k), with A006318 the large Schroeder numbers
`Nat.largeSchroder`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((Nat.choose k (n - k) : ℕ) : ℤ) * (Nat.largeSchroder k : ℤ)

/-- Mathar's conjecture: the recurrence holds for every n >= 5. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 1) * a n + (-5 * (n : ℤ) + 4) * a (n - 1) + (-11 * (n : ℤ) + 13) * a (n - 2) +
      3 * (-(n : ℤ) + 1) * a (n - 3) + 3 * ((n : ℤ) - 4) * a (n - 4) +
      ((n : ℤ) - 5) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a174808
