import Mathlib

/-!
# A Beatty frequency and the self-indexed word A082844

A097509 counts k ≥ 0 for which floor(k√2)−k equals the index.
For such a k one has k < (n+1)/(√2−1) < 3(n+1), giving a finite range.
A082844 starts with 3,2. At the position given by the first i terms'
sum it copies term i. Between two successive such positions the symbols
alternate between 2 and 3. The positive symbols and the initial terms
make this a deterministic rule: the first marked position is 3 and each
later one refers to an earlier term. The index shift in Irwin's conjecture
compares its term i with the frequency at i+1.

Bhargava, Kedlaya and Ng described the connection with Putnam 2020 B6.
Sources: https://oeis.org/A097509 and https://oeis.org/A082844
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a097509

noncomputable def frequency (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (3*(n+1))).filter
    (fun k : ℕ => ⌊(k : ℝ)*Real.sqrt 2⌋ - (k : ℤ) = (n : ℤ))).card

def sumFirst (s : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, s (j+1)

structure FollowsRule (s : ℕ → ℕ) : Prop where
  first : s 1 = 3
  second : s 2 = 2
  alphabet : ∀ n, 1 ≤ n → s n = 2 ∨ s n = 3
  marked : ∀ n, 1 ≤ n → s (sumFirst s n) = s n
  gaps : ∀ n j, 1 ≤ n → 0 < j → j < s (n+1) →
    s (sumFirst s n+j) = 5-s (sumFirst s n+j-1)

theorem main : FollowsRule (fun n => frequency (n+1)) := by
  sorry

end OMA.S_oeis_a097509
