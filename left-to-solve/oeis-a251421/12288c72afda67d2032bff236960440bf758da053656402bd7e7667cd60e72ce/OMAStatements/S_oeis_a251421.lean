import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Two parity formulas and the generating function for OEIS A251421

Source: https://oeis.org/A251421

The max-minus-twice-median-plus-min expression vanishes on constant triples
and has absolute value one on every other binary triple. Signs can give
sum zero exactly when the number of nonconstant triples is even. The count
records that parity while appending bits. The series starts at index one.
For odd n, the exponent (n-3)/2+1 is the same as the natural quotient n/2.
-/

namespace OMA.S_oeis_a251421

def nonconstant (x y z : Bool) : Bool :=
  if x then !(y && z) else y || z

/-- Count suffixes whose final parity is even. -/
def completions : ℕ → Bool → Bool → Bool → ℕ
  | 0, _, _, odd => if odd then 0 else 1
  | k + 1, x, y, odd =>
      completions k y false (Bool.xor odd (nonconstant x y false)) +
        completions k y true (Bool.xor odd (nonconstant x y true))

def countedWords (n : ℕ) : ℕ :=
  completions n false false false + completions n false true false +
    completions n true false false + completions n true true false

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else countedWords n

open PowerSeries in
theorem main :
    ((1 - 2 * X) * (1 - 2 * X ^ 2) * PowerSeries.mk (fun n => (a n : ℤ)) =
      2 * X * (1 + 4 * X - 8 * X ^ 2)) ∧
    (∀ n : ℕ, 0 < n → n % 2 = 0 → a n = 2 * (2 ^ (n / 2) + 2 ^ n)) ∧
    (∀ n : ℕ, 0 < n → n % 2 = 1 → a n = 2 * (2 ^ n - 2 ^ (n / 2))) := by
  sorry

end OMA.S_oeis_a251421
