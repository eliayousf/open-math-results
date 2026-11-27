import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! J. Lowell's observation on sums of two squares, from OEIS A001481. -/

namespace OpenMath.A001481

/-- Membership in A001481, with the nonnegative convention of the OEIS entry. -/
def SumTwoSquares (n : ℕ) : Prop := ∃ x y : ℕ, x ^ 2 + y ^ 2 = n

private theorem square_residues (x : ℕ) :
    ((x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 4) ∧ x % 2 = 0) ∨ x ^ 2 % 8 = 1 := by
  have h : ∀ r : Fin 8,
      ((r.val ^ 2 % 8 = 0 ∨ r.val ^ 2 % 8 = 4) ∧ r.val % 2 = 0) ∨ r.val ^ 2 % 8 = 1 := by
    decide
  rw [Nat.pow_mod x 2 8, ← Nat.mod_mod_of_dvd x (by decide : 2 ∣ 8)]
  exact h ⟨x % 8, Nat.mod_lt _ (by decide)⟩

private theorem all_even {a b c d : ℕ} (h : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) % 8 = 0) :
    a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 0 := by
  have ha := square_residues a
  have hb := square_residues b
  have hc := square_residues c
  have hd := square_residues d
  omega

private theorem small_exponent {k x y z w : ℕ} (hk : k < 3)
    (h : x ^ 2 + y ^ 2 + (z ^ 2 + w ^ 2) = 2 ^ k) :
    x ^ 2 + y ^ 2 = 0 ∨ z ^ 2 + w ^ 2 = 0 ∨ x ^ 2 + y ^ 2 = z ^ 2 + w ^ 2 := by
  have hp : ∀ r : Fin 3, 2 ^ r.val ≤ 4 := by decide
  have hsum : 2 ^ k ≤ 4 := hp ⟨k, hk⟩
  have hcoord (a : ℕ) (ha : a ^ 2 ≤ 4) : a < 3 := by
    by_contra! hge
    have hsq : 3 ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hge 2
    omega
  have hc : ∀ (k a b c d : Fin 3),
      a.val ^ 2 + b.val ^ 2 + (c.val ^ 2 + d.val ^ 2) = 2 ^ k.val →
        a.val ^ 2 + b.val ^ 2 = 0 ∨ c.val ^ 2 + d.val ^ 2 = 0 ∨
          a.val ^ 2 + b.val ^ 2 = c.val ^ 2 + d.val ^ 2 := by
    decide
  exact hc ⟨k, hk⟩ ⟨x, hcoord x (by omega)⟩ ⟨y, hcoord y (by omega)⟩
    ⟨z, hcoord z (by omega)⟩ ⟨w, hcoord w (by omega)⟩ h

private theorem four_squares (k x y z w : ℕ)
    (h : x ^ 2 + y ^ 2 + (z ^ 2 + w ^ 2) = 2 ^ k) :
    x ^ 2 + y ^ 2 = 0 ∨ z ^ 2 + w ^ 2 = 0 ∨ x ^ 2 + y ^ 2 = z ^ 2 + w ^ 2 := by
  induction k using Nat.strong_induction_on generalizing x y z w with
  | h k ih =>
    by_cases hk : k < 3
    · exact small_exponent hk h
    · have hk3 : 3 ≤ k := by omega
      have h8 : 8 ∣ (2 : ℕ) ^ k := by
        simpa only [show (2 : ℕ) ^ 3 = 8 by decide] using pow_dvd_pow (2 : ℕ) hk3
      have hm : (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) % 8 = 0 := by
        rw [Nat.add_assoc (x ^ 2 + y ^ 2), h, Nat.mod_eq_zero_of_dvd h8]
      obtain ⟨hx, hy, hz, hw⟩ := all_even hm
      have ex : x = 2 * (x / 2) := by omega
      have ey : y = 2 * (y / 2) := by omega
      have ez : z = 2 * (z / 2) := by omega
      have ew : w = 2 * (w / 2) := by omega
      have left_scale : x ^ 2 + y ^ 2 = 4 * ((x / 2) ^ 2 + (y / 2) ^ 2) := by
        nth_rw 1 [ex]
        nth_rw 1 [ey]
        ring
      have right_scale : z ^ 2 + w ^ 2 = 4 * ((z / 2) ^ 2 + (w / 2) ^ 2) := by
        nth_rw 1 [ez]
        nth_rw 1 [ew]
        ring
      have power_scale : (2 : ℕ) ^ k = 4 * 2 ^ (k - 2) := by
        calc
          _ = (2 : ℕ) ^ (2 + (k - 2)) := congrArg (fun j : ℕ => (2 : ℕ) ^ j) (by omega)
          _ = _ := by rw [pow_add]; rfl
      rw [left_scale, right_scale, power_scale] at h
      have hhalf : (x / 2) ^ 2 + (y / 2) ^ 2 + ((z / 2) ^ 2 + (w / 2) ^ 2) =
          2 ^ (k - 2) := by omega
      have hcases := ih (k - 2) (by omega) (x / 2) (y / 2) (z / 2) (w / 2) hhalf
      rw [left_scale, right_scale]
      omega

/-- A power of two split into two sums of squares has equal parts or a zero part. -/
theorem main (a b k : ℕ) (ha : SumTwoSquares a) (hb : SumTwoSquares b)
    (h : a + b = 2 ^ k) : a = 0 ∨ b = 0 ∨ a = b := by
  obtain ⟨x, y, rfl⟩ := ha
  obtain ⟨z, w, rfl⟩ := hb
  exact four_squares k x y z w h

/-- In particular, two positive parts must be equal. -/
theorem positive_parts_equal (a b k : ℕ) (ha : SumTwoSquares a) (hb : SumTwoSquares b)
    (ha_pos : 0 < a) (hb_pos : 0 < b) (h : a + b = 2 ^ k) : a = b := by
  have hcases := main a b k ha hb h
  omega

end OpenMath.A001481
