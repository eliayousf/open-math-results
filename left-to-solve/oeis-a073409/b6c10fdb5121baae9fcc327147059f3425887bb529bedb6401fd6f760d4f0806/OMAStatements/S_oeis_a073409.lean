import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.PrimeFin

/-! The largest-prime congruence for OEIS A073409. Source: https://oeis.org/A073409/internal -/

namespace OMA.S_oeis_a073409

open Finset

/-- The largest prime divisor of the reduced denominator in the source sequence. -/
noncomputable def a (n : ℕ) : ℕ := (bernoulli (2 * n)).den.primeFactors.sup id

theorem main : ∀ n : ℕ, 0 < n →
    IsGreatest {r : ℕ | r.Prime ∧ r ≤ 2*n+1 ∧
      ((r:ℤ)*(bernoulli (2*n)).num ≡ -((bernoulli (2*n)).den:ℤ) [ZMOD (r:ℤ)^2])} (a n) := by
  sorry

end OMA.S_oeis_a073409
