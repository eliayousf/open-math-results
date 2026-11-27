import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum

/-! Yanev's signed formula for OEIS A006364, using its increasing enumeration. -/

namespace OpenMath.A006364

/-- A000120, the number of ones in the binary expansion. -/
def bitCount (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- The binary digits above the last bit have even weight. -/
def Qualifies (m : ℕ) : Prop := bitCount (m / 2) % 2 = 0

/-- A006364, using the one-based index of the OEIS entry. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth Qualifies (n - 1)

private theorem bitCount_twice_add (k r : ℕ) (hr : r < 2) :
    bitCount (2 * k + r) = bitCount k + r := by
  by_cases hz : 2 * k + r = 0
  · have hk : k = 0 := by omega
    have hr' : r = 0 := by omega
    simp [hk, hr', bitCount, Nat.digits_zero]
  unfold bitCount
  rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 2) hz, List.sum_cons]
  rw [show (2 * k + r) / 2 = k by omega, show (2 * k + r) % 2 = r by omega]
  exact Nat.add_comm _ _

private theorem qualifies_block (k r : ℕ) (hr : r < 4) :
    Qualifies (4 * k + r) ↔ r / 2 = bitCount k % 2 := by
  unfold Qualifies
  rw [show (4 * k + r) / 2 = 2 * k + r / 2 by omega,
    bitCount_twice_add k (r / 2) (by omega)]
  omega

/-- A block of four contributes two consecutive terms to the enumeration. -/
private def blockValue (i : ℕ) : ℕ :=
  4 * (i / 2) + (2 * (bitCount (i / 2) % 2) + i % 2)

private theorem blockValue_qualifies (i : ℕ) : Qualifies (blockValue i) := by
  unfold blockValue
  exact (qualifies_block (i / 2) _ (by omega)).mpr (by omega)

private theorem blockValue_strictMono : StrictMono blockValue := by
  intro i j hij
  unfold blockValue
  by_cases h : i / 2 = j / 2
  · rw [h]
    omega
  · omega

private theorem blockValue_surjective (m : ℕ) (hm : Qualifies m) :
    ∃ i : ℕ, blockValue i = m := by
  have hblock : Qualifies (4 * (m / 4) + m % 4) := by
    simpa [show 4 * (m / 4) + m % 4 = m by omega] using hm
  have hbit := (qualifies_block (m / 4) (m % 4) (by omega)).mp hblock
  refine ⟨2 * (m / 4) + m % 2, ?_⟩
  unfold blockValue
  rw [show (2 * (m / 4) + m % 2) / 2 = m / 4 by omega,
    show (2 * (m / 4) + m % 2) % 2 = m % 2 by omega]
  omega

private theorem blockValue_eq_nth (i : ℕ) : blockValue i = Nat.nth Qualifies i := by
  have hinf : (Set.ofPred Qualifies).Infinite :=
    (Set.infinite_range_of_injective blockValue_strictMono.injective).mono (by
      rintro _ ⟨j, rfl⟩
      exact blockValue_qualifies j)
  apply Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn blockValue
  · intro m hm
    obtain ⟨j, hj⟩ := blockValue_surjective m hm
    exact ⟨j, fun h => (hinf h).elim, hj⟩
  · exact fun j _ => blockValue_qualifies j
  · exact blockValue_strictMono.strictMonoOn _
  · exact fun h => (hinf h).elim

private theorem sign_pow (m : ℕ) : (-1 : ℤ) ^ m = 1 - 2 * ((m % 2 : ℕ) : ℤ) := by
  rcases Nat.even_or_odd m with he | ho
  · have hr : m % 2 = 0 := Nat.even_iff.mp he
    simp [hr, he.neg_pow]
  · have hr : m % 2 = 1 := Nat.odd_iff.mp ho
    simp [hr, ho.neg_pow]

/-- The signed expression in Yanev's conjecture, at every positive index. -/
theorem main (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℤ) =
      2 * (n : ℤ) + (-1 : ℤ) ^ (n - bitCount (n - 1)) - (3 + (-1 : ℤ) ^ n) / 2 := by
  let k := (n - 1) / 2
  let e := (n - 1) % 2
  have hnr : n - 1 = 2 * k + e := by dsimp [k, e]; omega
  have he : e < 2 := by dsimp [e]; omega
  have hw : bitCount (n - 1) = bitCount k + e := by
    rw [hnr, bitCount_twice_add k e he]
  have hle : bitCount (n - 1) ≤ n - 1 := Nat.digit_sum_le 2 (n - 1)
  have hsign₁ : (-1 : ℤ) ^ (n - bitCount (n - 1)) = 2 * ((bitCount k % 2 : ℕ) : ℤ) - 1 := by
    rw [sign_pow]
    omega
  have hsign₂ : (-1 : ℤ) ^ n = 2 * (e : ℤ) - 1 := by
    rw [sign_pow]
    omega
  rw [a, ← blockValue_eq_nth, hsign₁, hsign₂]
  unfold blockValue
  change ((4 * k + (2 * (bitCount k % 2) + e) : ℕ) : ℤ) = _
  omega

end OpenMath.A006364
