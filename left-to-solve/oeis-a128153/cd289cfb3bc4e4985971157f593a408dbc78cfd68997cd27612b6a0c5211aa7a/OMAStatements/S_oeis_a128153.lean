import Mathlib

/-!
# The number of regular pentagons in Priluck's second construction

Sources: https://oeis.org/A128153 and https://oeis.org/A128127/a128127.pdf.

For n > 0 put m = n + 1 and take the original apothem to be m.
Project onto the five outward unit normals in cyclic order. The projections
of the outer vertices in any one direction are m, m, (φ−2)m, (2−2φ)m,
(φ−2)m, where φ is the golden ratio. Boundary subdivision gives two
progressions of possible supporting lines. The shared endpoint is assigned
to the first progression.

A pentagon with these five unoriented directions is a translated signed
dilate of the original pentagon. Its side offsets are y_j = x_j + h,
where x_j are the center projections and h is its signed apothem.
The condition that y_(j−1) + y_(j+1) − (φ−1)y_j be constant is exactly
the center-projection condition after taking h to be the average offset.
It is expressed as equality of both integer coefficients in Q(φ).
Positive dilates are contained because all offsets are at most m.
For a negative dilate the greatest projection in direction j is
y_j − (2φ−1)h, so containment requires those five bounds.
The original paper sets the count at n = 0 separately to one.
-/

namespace OMA.S_oeis_a128153

noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

abbrev Offset (m : ℕ) := Fin (m + 1) ⊕ Fin m

def coefficients (m : ℕ) : Offset m → ℤ × ℤ
  | .inl k => ((m : ℤ) - 3 * k.val, k.val)
  | .inr k => (-2 * (m : ℤ) + 4 * (k.val + 1), (m : ℤ) - 3 * (k.val + 1))

noncomputable def value (m : ℕ) (k : Offset m) : ℝ :=
  (coefficients m k).1 + (coefficients m k).2 * phi

def shift (i : Fin 5) (k : ℕ) : Fin 5 := ⟨(i.val + k) % 5, Nat.mod_lt _ (by decide)⟩

def residual (m : ℕ) (p : Fin 5 → Offset m) (i : Fin 5) : ℤ × ℤ :=
  let left := coefficients m (p (shift i 4))
  let right := coefficients m (p (shift i 1))
  let middle := coefficients m (p i)
  (left.1 + right.1 + middle.1 - middle.2, left.2 + right.2 - middle.1)

noncomputable def apothem (m : ℕ) (p : Fin 5 → Offset m) : ℝ :=
  (∑ i : Fin 5, value m (p i)) / 5

def Valid (m : ℕ) (p : Fin 5 → Offset m) : Prop :=
  (∀ i, residual m p i = residual m p 0) ∧
  (0 < apothem m p ∨
    (apothem m p < 0 ∧ ∀ i, value m (p i) - (2 * phi - 1) * apothem m p ≤ m))

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 1 else Nat.card { p : Fin 5 → Offset (n + 1) // Valid (n + 1) p }

open PowerSeries in
theorem main :
    (∀ n : ℕ, 0 < n → 4 * (a n : ℤ) =
      10 * (n : ℤ)^2 + 16 * n + 9 - (-1 : ℤ)^n) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) =
      2 * (a (n - 1) : ℤ) - 2 * (a (n - 3) : ℤ) + a (n - 4)) ∧
    (((X : PowerSeries ℤ) - 1)^3 * (X + 1) * PowerSeries.mk (fun n => (a n : ℤ)) =
        -X^4 + X^3 - 2*X^2 - 7*X - 1) := by
  sorry

end OMA.S_oeis_a128153
