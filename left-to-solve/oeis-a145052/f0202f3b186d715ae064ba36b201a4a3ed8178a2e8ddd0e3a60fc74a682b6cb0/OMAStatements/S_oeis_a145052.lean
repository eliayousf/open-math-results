import Mathlib

/-!
# Generating function and closed form for OEIS A145052

Source: https://oeis.org/A145052
The nonnegative arrays with each consecutive 3-by-3 block summing to one have
only entries zero or one, since every cell belongs to at least one such block
when the dimension is at least three. Coefficients below the offset 3 are zero.
In the closed form, the source quantity `3 ^ (n / 3) / 3` is written as
`3 ^ (n / 3 - 1)`, which is equal on the domain `3 ≤ n`.
-/

namespace OMA.S_oeis_a145052

/-- A square array in which every consecutive three-by-three block sums to one. -/
def Valid {n : ℕ} (a : Fin n → Fin n → Fin 2) : Prop :=
  ∀ i j : ℕ, ∀ hi : i + 2 < n, ∀ hj : j + 2 < n,
    ∑ r : Fin 3, ∑ c : Fin 3,
      (a ⟨i + r, by omega⟩ ⟨j + c, by omega⟩).val = 1

/-- The sequence counts one third of the arrays at each dimension in its domain. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n < 3 then 0 else Nat.card { arr : Fin n → Fin n → Fin 2 // Valid arr } / 3

open PowerSeries

theorem main :
    ((1 - X - 3 * X ^ 3 + 3 * X ^ 4) * PowerSeries.mk (fun n => (a n : ℤ)) =
      X ^ 3 * (3 + 4 * X + 4 * X ^ 2 - 5 * X ^ 3)) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = (6 + 4 * ((n % 3 : ℕ) : ℤ)) * 3 ^ (n / 3 - 1) - 3) := by
  sorry

end OMA.S_oeis_a145052
