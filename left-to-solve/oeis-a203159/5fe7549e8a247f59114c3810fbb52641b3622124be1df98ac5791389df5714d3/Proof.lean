import OMAStatements.S_oeis_a203159
import Mathlib.Tactic.Ring

namespace OpenMath.A203159

open OMA.S_oeis_a203159

private theorem step (n : ℕ) :
    products (n + 1) = ((products n).1 * (2 * ((n : ℤ) + 1)),
      (products n).2 * (2 * ((n : ℤ) + 1)) + (products n).1) := by
  change (let (p,e) := products n; (p * (2 * ((n : ℤ) + 1)), e * (2 * ((n : ℤ) + 1)) + p)) = _
  cases products n; rfl

private theorem shift_recur (n : ℕ) :
    a (n + 2) = (4 * (n : ℤ) + 6) * a (n + 1) - 4 * ((n : ℤ) + 1)^2 * a n := by
  unfold a
  rw [step (n + 1), step n]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem main : ∀ n : ℕ, 2 < n →
    a n + 2 * (-2 * (n : ℤ) + 1) * a (n - 1) +
      4 * ((n : ℤ) - 1) ^ 2 * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, shift_recur]
  push_cast
  ring

end OpenMath.A203159

theorem OMA.solution : type_of% @OMA.S_oeis_a203159.main := OpenMath.A203159.main
