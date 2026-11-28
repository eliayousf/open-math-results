import Mathlib

/-!
# A094759: Least k <= n such that n * sigma(k) = k * sigma(n)

Source: https://oeis.org/A094759
Credit: @AkiRA-COM-FP

Formalizes the OEIS A094759 conjecture (offset 1): there are infinitely many positive
integers `n` such that `a(n) < n`, where `a(n)` is the least positive integer `k <= n`
with `n * sigma(k) = k * sigma(n)`.
-/

namespace OMA.S_oeis_a094759

/-- The OEIS sequence A094759: least positive integer `k <= n` such that
`n * sigma(k) = k * sigma(n)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ k ≤ n ∧
    n * ArithmeticFunction.sigma 1 k = k * ArithmeticFunction.sigma 1 n}

/-- There are infinitely many positive integers `n` with `a(n) < n`. -/
theorem main :
    Set.Infinite {n : ℕ | 1 ≤ n ∧ a n < n} := by
  sorry

end OMA.S_oeis_a094759
