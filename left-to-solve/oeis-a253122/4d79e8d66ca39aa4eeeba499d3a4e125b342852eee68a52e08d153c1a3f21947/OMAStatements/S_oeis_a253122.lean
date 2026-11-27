import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Two parity formulas and the generating function for OEIS A253122

Source: https://oeis.org/A253122

Each median is zero or one. Signs can give sum zero exactly when the number
of ones is even, since the ones must receive equal numbers of plus and minus
signs. Each recursive call appends either bit and records the parity after
counting the median of the new triple. The series starts at index one.
-/

namespace OMA.S_oeis_a253122

def median (x y z : Bool) : Bool :=
  if x then y || z else y && z

/-- Count suffixes whose final parity is even. -/
def completions : ℕ → Bool → Bool → Bool → ℕ
  | 0, _, _, odd => if odd then 0 else 1
  | k + 1, x, y, odd =>
      completions k y false (Bool.xor odd (median x y false)) +
        completions k y true (Bool.xor odd (median x y true))

def countedWords (n : ℕ) : ℕ :=
  completions n false false false + completions n false true false +
    completions n true false false + completions n true true false

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else countedWords n

open PowerSeries in
theorem main :
    ((1 - 2 * X) * (1 - 2 * X ^ 2) * PowerSeries.mk (fun n => (a n : ℤ)) =
      4 * X * (1 + X - 4 * X ^ 2)) ∧
    (∀ n : ℕ, 0 < n → n % 2 = 0 → a n = 2 ^ (n / 2 + 1) + 2 ^ (n + 1)) ∧
    (∀ n : ℕ, 0 < n → n % 2 = 1 → a n = 2 ^ (n + 1)) := by
  sorry

end OMA.S_oeis_a253122
