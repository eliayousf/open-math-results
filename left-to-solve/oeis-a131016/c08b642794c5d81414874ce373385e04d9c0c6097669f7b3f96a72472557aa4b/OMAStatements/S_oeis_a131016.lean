import Mathlib

/-!
# A131016: Smallest semiprime == 1 (mod n)

Source: https://oeis.org/A131016
Credit: @AkiRA-COM-FP

Formalizes the OEIS A131016 conjecture (offset 1): every semiprime occurs in the sequence
`a(n)` of smallest semiprimes congruent to `1` modulo `n`.
-/

namespace OMA.S_oeis_a131016

/-- A natural number is a semiprime if it is the product of two primes (not necessarily distinct). -/
def IsSemiprime (m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q

/-- The OEIS sequence A131016: smallest semiprime congruent to `1` modulo `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | IsSemiprime m ∧ m ≡ 1 [MOD n]}

/-- Every semiprime occurs in the sequence A131016 for some `n >= 1`. -/
theorem main :
    ∀ s : ℕ, IsSemiprime s → ∃ n : ℕ, 1 ≤ n ∧ a n = s := by
  sorry

end OMA.S_oeis_a131016
