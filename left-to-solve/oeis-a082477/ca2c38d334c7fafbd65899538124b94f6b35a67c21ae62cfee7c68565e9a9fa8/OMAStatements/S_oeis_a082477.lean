import Mathlib

/-!
# Mean number of adjacent divisors of adjacent integers

Amiram Eldar's conjecture of June 4, 2022 in https://oeis.org/A082477.
The sequence starts at one. Each positive divisor d of n qualifies when d+1 divides n+1.
-/
namespace OMA.S_oeis_a082477
open Filter Topology

def term (n : ℕ) : ℕ := (n.divisors.filter (fun d => d+1 ∣ n+1)).card

theorem main :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, (term (k+1) : ℝ)) / N)
      atTop (𝓝 2) := by
  sorry

end OMA.S_oeis_a082477
