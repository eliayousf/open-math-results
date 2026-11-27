import Mathlib

/-!
# A045797: a linear recurrence for the evenish numbers

Source: https://oeis.org/A045797 (OEIS Foundation, CC BY-SA 4.0).

Evenish numbers are the positive integers that are prime to 10 and whose tens
digit is even; a(n) is the n-th of them (offset 1, so a(1), ..., a(5) = 1, 3, 7, 9, 21).
Colin Barker (Apr 14 2012) conjectured that a(n) = a(n-1) + a(n-4) - a(n-5).
The recurrence involves a(n-5), so it is stated for n >= 6.

The tens digit of k is (k / 10) mod 10, whose parity is that of k / 10.
Since 0 is not prime to 10, every term is positive.
-/

namespace OMA.S_oeis_a045797

/-- `k` is prime to 10 and its tens digit is even. -/
def evenish (k : ℕ) : Prop := Nat.Coprime k 10 ∧ (k / 10 % 10) % 2 = 0

/-- `a n` is the `n`-th evenish number, counting from `a 1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth evenish (n - 1)

theorem main : ∀ n : ℕ, 6 ≤ n →
    (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5) := by
  sorry

end OMA.S_oeis_a045797
