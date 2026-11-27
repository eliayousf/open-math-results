import Mathlib.Data.Int.Basic

/-!
# Exceptional indices of the OEIS A076217 recurrence

Source: https://oeis.org/A076217
Bill McEachen's 21 March 2025 comment proposes that the linear recurrence
fails exactly at a power of three and the next two indices, starting at nine.
-/

namespace OMA.S_oeis_a076217

/-- The signed update from OEIS, with a zero term adjoined to obtain one-based indexing. -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => a n + (n + 1 : ℕ) * Int.sign ((n + 1 : ℕ) - a n)

theorem main :
    ∀ n : ℕ, 5 < n →
      ((a n = -a (n - 1) + a (n - 2) + a (n - 3)) ↔
        ¬ ∃ k : ℕ, 2 ≤ k ∧ 3 ^ k ≤ n ∧ n < 3 ^ k + 3) := by
  sorry

end OMA.S_oeis_a076217
