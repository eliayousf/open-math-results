import Mathlib

/-!
# OEIS A068912

Source: https://oeis.org/A068912
Credit: @mbilenko03

Number of `n`-step walks with steps `±1`, starting at `0`, that are never more than `3`
or less than `-3`. A walk is a function `Fin n → Bool`, where `true` means `+1` and
`false` means `-1`. The partial sums of the first `k` steps, for every `k ≤ n`
(including the empty sum at the start), all lie in `[-3, 3]`.

The sequence begins `1, 2, 4, 8, 14, 28, 48, 96` at offset `0`.

Peter Luschny conjectured on 20 September 2020 that
`a n = ⌊(1 + r) ^ (n / 2) * (r + √(2 * (1 + r)) + (-1) ^ n * (r - √(2 * (1 + r)))) / 4⌋`
where `r = 1 + √2`.
-/

namespace OMA.S_oeis_a068912

/-- A step of `+1` (`true`) or `-1` (`false`). -/
def step (b : Bool) : ℤ :=
  if b then 1 else -1

/-- Sum of those steps of `w` whose index is strictly less than `k`. -/
def partialSum {n : ℕ} (w : Fin n → Bool) (k : ℕ) : ℤ :=
  ∑ j : Fin n, if j.val < k then step (w j) else 0

/-- Every partial sum with at most `n` steps lies in `[-3, 3]`. -/
def stays {n : ℕ} (w : Fin n → Bool) : Prop :=
  ∀ k : Fin (n + 1), -3 ≤ partialSum w k.val ∧ partialSum w k.val ≤ 3

instance {n : ℕ} (w : Fin n → Bool) : Decidable (stays w) := by
  unfold stays
  infer_instance

/-- The number of `n`-step walks from `0` that stay inside `[-3, 3]`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → Bool => stays w).card

/-- Luschny's constant `r = 1 + √2`. -/
noncomputable def r : ℝ :=
  1 + Real.sqrt 2

/-- Luschny's closed form for the walk count. -/
noncomputable def luschny (n : ℕ) : ℝ :=
  ((1 + r) ^ ((n : ℝ) / 2) *
      (r + Real.sqrt (2 * (1 + r)) +
        (-1 : ℝ) ^ n * (r - Real.sqrt (2 * (1 + r))))) /
    4

/-- Luschny's conjecture: the walk count is the floor of that closed form. -/
theorem main : ∀ n : ℕ, (a n : ℤ) = ⌊luschny n⌋ := by
  sorry

end OMA.S_oeis_a068912
