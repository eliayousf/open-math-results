import Mathlib

/-!
# Parity of the terms of OEIS A048868

Michael De Vlieger conjectured that every positive integer whose reduced
residue system contains more primes than nonprimes is even.
We use the representatives from 1 through n, as in the OEIS entry.

Source: https://oeis.org/A048868
Credit: @DrSubspace
-/

namespace OMA.S_oeis_a048868

def reducedResidues (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun k => k.Coprime n)

theorem main : ∀ n : ℕ, 0 < n →
    ((reducedResidues n).filter (fun k => ¬ k.Prime)).card <
      ((reducedResidues n).filter Nat.Prime).card → Even n := by
  sorry

end OMA.S_oeis_a048868
