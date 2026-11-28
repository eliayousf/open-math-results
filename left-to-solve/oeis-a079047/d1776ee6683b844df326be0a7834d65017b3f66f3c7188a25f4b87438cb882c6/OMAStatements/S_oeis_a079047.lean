import Mathlib

/-!
# A079047: Number of primes between prime(n) and prime(n)^2.

Source: https://oeis.org/A079047
Credit: @matchalabubu15

Conjecture, as written in the OEIS entry:
"I conjecture that 25 and 64 are the only terms that are also square numbers."

Conventions:
* The OEIS offset is 1: `a 1` corresponds to prime(1) = 2. Only indices `n ≥ 1` are terms.
* "Between" means strictly between. This matches the OEIS example a(1) = 1 and the
  Mathematica program `PrimePi[p^2] - n`.

Caveats about the source (the statement is deliberately not altered to avoid them):
* a(1) = 1 is itself a square.
* T. D. Noe (Sep 11 2013) reported in the same entry the squares 564001 and 774400,
  at n = 419 and n = 481.
-/

namespace OMA.S_oeis_a079047

/-- A079047: the number of primes strictly between prime(n) and prime(n)^2, for `n ≥ 1`.
`Nat.nth Nat.Prime` counts from 0, so prime(n) is `Nat.nth Nat.Prime (n - 1)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  let p := Nat.nth Nat.Prime (n - 1)
  ((Finset.Ioo p (p ^ 2)).filter Nat.Prime).card

/-- 25 and 64 are the only terms of the sequence that are also square numbers. -/
theorem main : {m : ℕ | (∃ n, 1 ≤ n ∧ a n = m) ∧ IsSquare m} = {25, 64} := by
  sorry

end OMA.S_oeis_a079047
