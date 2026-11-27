import Mathlib.Order.Lattice.Nat
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Colin Barker's closed form, recurrence, and generating function for A088039

Source: https://oeis.org/A088039
-/

namespace OMA.S_oeis_a088039

def candidates (n : ℕ) : Set ℕ :=
  {k | 1 < k ∧ ∃ b : ℕ, 1 < b ∧ b ^ n ∣ k ^ 3 - 1}

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else sInf (candidates n)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 2 < n → a n = 2 ^ n + 1) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * (a (n-1) : ℤ) - 2 * (a (n-2) : ℤ)) ∧
    ((1 - X) * (1 - 2 * X) * mk (fun n => (a n : ℤ)) =
      2 * X - 2 * X ^ 2 + X ^ 3 - 2 * X ^ 4) := by
  sorry

end OMA.S_oeis_a088039
