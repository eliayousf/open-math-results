import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A025093: a(n) = s(1)t(n) + s(2)t(n-1) + ... + s(k)t(n-k+1), s = Lucas numbers, t = odd numbers

Source: https://oeis.org/A025093
Credit: @SPatel2133

Conjectures of Colin Barker, 7 August 2019:
G.f.: x*(3 - x + 9*x^2 - 7*x^3 - 5*x^4 - x^5 - 2*x^6 - 2*x^7) / ((1 - x)^2*(1 - x^2 - x^4)^2), and
a(n) = 2*a(n-1) + a(n-2) - 4*a(n-3) + 3*a(n-4) - 2*a(n-5) - a(n-6) + 4*a(n-7) - 3*a(n-8)
  + 2*a(n-9) - a(n-10) for n > 10.

The name gives k = [n/2] and t = (odd natural numbers), and the sequence has offset one. With
t(j) = 2*j - 1 the name's sum at index n + 1 equals the listed term a(n): the listed terms
3, 5, 22, 30, 66, 82, ... are a(n) = sum_{i=1}^{floor((n+1)/2)} L(i)*(2*(n-i)+3), where L(1) = 1,
L(2) = 3 are the Lucas numbers. This reading is fixed by the listed data (all 40 terms of the
b-file agree); the name's sum taken literally at index n does not give the listed terms.
The definition gives a(0) = 0, the constant coefficient of the conjectured generating function,
whose denominator is cleared.
-/

namespace OMA.S_oeis_a025093

open PowerSeries

def L : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => L (n + 1) + L n

def a (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc 1 ((n + 1) / 2), L i * (2 * ((n : ℤ) - i) + 3)

theorem main :
    (∀ n : ℕ, 10 < n →
      a n = 2 * a (n - 1) + a (n - 2) - 4 * a (n - 3) + 3 * a (n - 4) - 2 * a (n - 5) -
        a (n - 6) + 4 * a (n - 7) - 3 * a (n - 8) + 2 * a (n - 9) - a (n - 10)) ∧
    ((1 - X) ^ 2 * (1 - X ^ 2 - X ^ 4) ^ 2 * PowerSeries.mk a =
      (X * (3 - X + 9 * X ^ 2 - 7 * X ^ 3 - 5 * X ^ 4 - X ^ 5 - 2 * X ^ 6 - 2 * X ^ 7) :
        PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a025093
