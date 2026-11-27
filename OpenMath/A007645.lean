import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Tisdale's union identity for generalized cuban primes, OEIS A007645. -/

namespace OpenMath.A007645

def GeneralizedCubanPrime (p : ℕ) : Prop := p.Prime ∧ (p % 3 = 0 ∨ p % 3 = 1)

def IsA002383 (p : ℕ) : Prop := p.Prime ∧ ∃ k : ℕ, p = k ^ 2 + k + 1

def IsA162471 (p : ℕ) : Prop :=
  (p.Prime ∧ ∃ k : ℕ, p ∣ k ^ 2 + k + 1) ∧ ¬ IsA002383 p

private theorem quadratic_divisors (p : ℕ) (hp : p.Prime) :
    (p % 3 = 0 ∨ p % 3 = 1) ↔ ∃ k : ℕ, p ∣ k ^ 2 + k + 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hthree : Nat.Prime 3 := by decide
  constructor
  · rintro (h | h)
    · have hp3 := (Nat.prime_dvd_prime_iff_eq hthree hp).mp (Nat.dvd_of_mod_eq_zero h)
      subst p
      exact ⟨1, by decide⟩
    · have hd : 3 ∣ Fintype.card (ZMod p)ˣ := by rw [hcard]; omega
      let _ : Fact (Nat.Prime 3) := ⟨hthree⟩
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (ZMod p)ˣ) 3 hd
      have hcube : (u : ZMod p) ^ (3 : ℕ) = 1 := by
        have hpow : u ^ (3 : ℕ) = 1 := hu ▸ pow_orderOf_eq_one u
        change (Units.coeHom (ZMod p) u) ^ (3 : ℕ) = 1
        rw [← map_pow, hpow, map_one]
      have hne : (u : ZMod p) ≠ 1 := by
        intro h
        have hunit : u = 1 := Units.ext h
        rw [hunit, orderOf_one] at hu
        omega
      have hmul : ((u : ZMod p) - 1) * ((u : ZMod p) ^ 2 + u + 1) = 0 := by
        calc
          _ = (u : ZMod p) ^ 3 - 1 := by ring
          _ = 0 := by rw [hcube, sub_self]
      have hz := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)
      refine ⟨(u : ZMod p).val, (ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, ZMod.natCast_zmod_val] using hz
  · rintro ⟨k, hk⟩
    by_cases hp3 : p = 3
    · subst p
      exact Or.inl (by decide)
    · let z : ZMod p := k
      have hz : z ^ 2 + z + 1 = 0 := by
        simpa only [z, Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
          (ZMod.natCast_eq_zero_iff _ _).mpr hk
      have hnonzero : z ≠ 0 := by
        intro h
        simp [h] at hz
      have hne : z ≠ 1 := by
        intro h
        have hz3 : (3 : ZMod p) = 0 := by
          rw [h] at hz
          calc
            (3 : ZMod p) = (1 : ZMod p) ^ 2 + 1 + 1 := by ring
            _ = 0 := hz
        have hdiv : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using hz3)
        exact hp3 ((Nat.prime_dvd_prime_iff_eq hp hthree).mp hdiv)
      let u := Units.mk0 z hnonzero
      have hcube : u ^ 3 = 1 := by
        apply Units.ext
        change z ^ 3 = 1
        calc
          z ^ 3 = (z - 1) * (z ^ 2 + z + 1) + 1 := by ring
          _ = 1 := by rw [hz, mul_zero, zero_add]
      have hu3 : orderOf u = 3 :=
        ((Nat.dvd_prime hthree).mp (orderOf_dvd_of_pow_eq_one hcube)).resolve_left <| by
          intro hu
          apply hne
          exact congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) (orderOf_eq_one_iff.mp hu)
      have hd : orderOf u ∣ Fintype.card (ZMod p)ˣ := orderOf_dvd_card
      rw [hu3, hcard] at hd
      exact Or.inr (by have := hp.two_le; omega)

/-- A007645 is the union of A002383 and A162471, interpreted as sets of primes. -/
theorem main (p : ℕ) : GeneralizedCubanPrime p ↔ IsA002383 p ∨ IsA162471 p := by
  classical
  constructor
  · rintro ⟨hp, h⟩
    by_cases he : IsA002383 p
    · exact Or.inl he
    · exact Or.inr ⟨⟨hp, (quadratic_divisors p hp).mp h⟩, he⟩
  · rintro (⟨hp, k, hk⟩ | ⟨⟨hp, h⟩, _⟩)
    · exact ⟨hp, (quadratic_divisors p hp).mpr ⟨k, hk ▸ dvd_rfl⟩⟩
    · exact ⟨hp, (quadratic_divisors p hp).mpr h⟩

end OpenMath.A007645
