import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic.LinearCombination

/-! Mathar's recurrence for the number of even involutions, OEIS A000704. -/

namespace OpenMath.A000704

open Finset

/-- The count of involutions on `n` labels with exactly `k` transpositions. -/
def matchings (n k : ℕ) : ℕ :=
  n.choose (2 * k) * (2 * k - 1).doubleFactorial

/-- The binomial and double factorial formula for A000704. -/
def a (n : ℕ) : ℕ := ∑ j ∈ range (n / 4 + 1), matchings n (2 * j)

private def oddCount (n : ℕ) : ℕ := ∑ j ∈ range (n / 4 + 1), matchings n (2 * j + 1)

private theorem matchings_zero (n : ℕ) : matchings n 0 = 1 := by
  simp [matchings]

private theorem matchings_vanish (n k : ℕ) (h : n < 2 * k) : matchings n k = 0 := by
  simp [matchings, Nat.choose_eq_zero_of_lt h]

private theorem matchings_step (n k : ℕ) :
    matchings (n + 2) (k + 1) = matchings (n + 1) (k + 1) + (n + 1) * matchings n k := by
  unfold matchings
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, Nat.doubleFactorial_add_one,
    show 2 * (k + 1) = 2 * k + 1 + 1 by omega, Nat.choose_succ_succ' (n + 1) (2 * k + 1)]
  rw [Nat.add_mul, ← Nat.mul_assoc ((n + 1).choose (2 * k + 1)), ← Nat.add_one_mul_choose_eq]
  ring

private theorem sum_extend (f : ℕ → ℕ) {m N : ℕ} (h : m ≤ N)
    (hf : ∀ k, m ≤ k → f k = 0) :
    (∑ k ∈ range m, f k) = ∑ k ∈ range N, f k := by
  apply Finset.sum_subset (range_mono h)
  intro k _ hk
  exact hf k (Nat.le_of_not_gt fun hlt => hk (mem_range.mpr hlt))

private theorem even_sum (n N : ℕ) (h : n / 4 + 1 ≤ N) :
    a n = ∑ k ∈ range N, matchings n (2 * k) := by
  apply sum_extend _ h
  intro k hk
  exact matchings_vanish _ _ (by omega)

private theorem odd_sum (n N : ℕ) (h : n / 4 + 1 ≤ N) :
    oddCount n = ∑ k ∈ range N, matchings n (2 * k + 1) := by
  apply sum_extend _ h
  intro k hk
  exact matchings_vanish _ _ (by omega)

private theorem even_step (n : ℕ) : a (n + 2) = a (n + 1) + (n + 1) * oddCount n := by
  have h (m : ℕ) (hm : m / 4 + 1 ≤ n + 3) :
      a m = (∑ k ∈ range (n + 2), matchings m (2 * (k + 1))) + 1 := by
    rw [even_sum m (n + 3) hm, sum_range_succ' _ (n + 2), mul_zero, matchings_zero]
  rw [h (n + 2) (by omega), h (n + 1) (by omega), odd_sum n (n + 2) (by omega), mul_sum]
  have hl (k : ℕ) : matchings (n + 2) (2 * (k + 1)) =
      matchings (n + 1) (2 * (k + 1)) + (n + 1) * matchings n (2 * k + 1) := by
    simpa only [show 2 * k + 1 + 1 = 2 * (k + 1) by omega] using matchings_step n (2 * k + 1)
  simp only [hl, sum_add_distrib]
  ring

private theorem odd_step (n : ℕ) : oddCount (n + 2) = oddCount (n + 1) + (n + 1) * a n := by
  rw [odd_sum (n + 2) (n + 3) (by omega), odd_sum (n + 1) (n + 3) (by omega),
    even_sum n (n + 3) (by omega), mul_sum]
  simp only [matchings_step, sum_add_distrib]

private theorem shifted (n : ℕ) :
    (a (n + 5) : ℤ) - 3 * a (n + 4) + 3 * a (n + 3) - a (n + 2) -
      ((n : ℤ) + 4) * ((n : ℤ) + 2) * a (n + 1) + ((n : ℤ) + 2) * ((n : ℤ) + 1) * a n = 0 := by
  have e₁ : (a (n + 5) : ℤ) = a (n + 4) + ((n : ℤ) + 4) * oddCount (n + 3) := by
    exact_mod_cast even_step (n + 3)
  have e₂ : (a (n + 4) : ℤ) = a (n + 3) + ((n : ℤ) + 3) * oddCount (n + 2) := by
    exact_mod_cast even_step (n + 2)
  have e₃ : (a (n + 3) : ℤ) = a (n + 2) + ((n : ℤ) + 2) * oddCount (n + 1) := by
    exact_mod_cast even_step (n + 1)
  have o₁ : (oddCount (n + 3) : ℤ) = oddCount (n + 2) + ((n : ℤ) + 2) * a (n + 1) := by
    exact_mod_cast odd_step (n + 1)
  have o₂ : (oddCount (n + 2) : ℤ) = oddCount (n + 1) + ((n : ℤ) + 1) * a n := by
    exact_mod_cast odd_step n
  linear_combination e₁ - 2 * e₂ + e₃ + ((n : ℤ) + 4) * o₁ - ((n : ℤ) + 2) * o₂

/-- The OEIS recurrence, for every index at which all six terms are defined. -/
theorem main (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℤ) - 3 * a (n - 1) + 3 * a (n - 2) - a (n - 3) -
      ((n : ℤ) - 1) * ((n : ℤ) - 3) * a (n - 4) +
        ((n : ℤ) - 3) * ((n : ℤ) - 4) * a (n - 5) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 5 + k = k + 5 by omega,
    show k + 5 - 1 = k + 4 by omega,
    show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega,
    show k + 5 - 4 = k + 1 by omega,
    show k + 5 - 5 = k by omega]
  push_cast
  linear_combination shifted k

end OpenMath.A000704
