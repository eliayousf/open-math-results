import Mathlib.Data.Int.Basic

/-!
# Priluck's proposed hexagon count in the class n = 2 modulo 3

Sources: https://oeis.org/A128828 and https://oeis.org/A128127/a128127.pdf.

Scale the original apothem to m = n + 1. In each of the three unoriented
normal directions, the supporting lines have integer coordinates from
−m to m, except 0, which is excluded in the construction without vertex
chords. The two outer sides are included.

Choose the three oriented normals N₀, N₁, N₂ spaced by 60 degrees, with
N₀ + N₂ = N₁. A translated regular hexagon of apothem h then has center
projections x, x+y, y and paired supporting-line coordinates x ± h,
(x+y) ± h, y ± h. The relation between the three positive-side offsets
forces h to be integral, hence x and y are integral too. The condition
that all six side offsets are allowed is equivalent to each of x, y,
and x+y lying between h−m and m−h and avoiding the two values ±h.
-/

namespace OMA.S_oeis_a128828

def centerList (m h : ℕ) : List ℤ :=
  (List.range (2 * (m - h) + 1)).map (fun (i : ℕ) => (i : ℤ) - ((m - h : ℕ) : ℤ))

def allowed (m h : ℕ) (z : ℤ) : Bool :=
  decide (-(↑(m-h : ℕ) : ℤ) ≤ z ∧ z ≤ ↑(m-h : ℕ) ∧ z ≠ ↑h ∧ z ≠ -(↑h : ℤ))

def countAt (m h : ℕ) : ℕ :=
  (centerList m h).foldl (fun total x =>
    (centerList m h).foldl (fun subtotal y =>
      if allowed m h x && allowed m h y && allowed m h (x + y)
      then subtotal + 1 else subtotal) total) 0

def a (n : ℕ) : ℕ :=
  ((List.range (n+1)).map (fun i => countAt (n+1) (i+1))).sum

theorem main : ∀ (n : ℕ), n % 3 = 2 →
    108 * (a n : ℤ) = 5 * (n : ℤ)^4 - 46 * (n : ℤ)^3 +
      1515 * (n : ℤ)^2 - 6046 * n + 7940 := by
  sorry

end OMA.S_oeis_a128828
