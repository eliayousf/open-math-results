import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient

/-!
MathOverflow 254323 asks whether the number of divisors of 2^n - 1 always
 divides its Euler totient, for every integer n >= 1.
Source: https://mathoverflow.net/questions/254323

The conjecture is false. The witness n = 253 was reported by user41593
in a comment on November 9, 2016. The accompanying disproof verifies
this witness, including every primality claim, and does not claim
minimality. At this witness the divisor count is 192 and the totient
has remainder 128 modulo 192.
-/

namespace OMA.S_mo_254323

theorem main : ∀ n : ℕ, 1 ≤ n →
    (2 ^ n - 1).divisors.card ∣ Nat.totient (2 ^ n - 1) := by
  sorry

end OMA.S_mo_254323
