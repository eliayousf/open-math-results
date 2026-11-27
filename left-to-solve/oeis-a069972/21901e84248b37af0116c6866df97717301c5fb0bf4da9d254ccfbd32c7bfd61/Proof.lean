import OMAStatements.S_oeis_a069972
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.PowerSeries.Basic

namespace OpenMath.A069972

open Finset

open OMA.S_oeis_a069972 (a lambert triangular)

private theorem twice_triangular (d : ℕ) : 2 * triangular d = d * (d + 1) := by
  have h : (d * (d + 1)) % 2 = 0 := by
    rw [Nat.mul_mod]
    have hb : d % 2 = 0 ∨ (d + 1) % 2 = 0 := by omega
    rcases hb with h | h <;> simp [h]
  unfold triangular
  omega

private theorem triangular_ge (d : ℕ) (hd : 0 < d) : d ≤ triangular d := by
  have h := Nat.mul_le_mul_left d (show 2 ≤ d + 1 by omega)
  rw [← twice_triangular, Nat.mul_comm d 2] at h
  omega

private theorem divisor_iff (d n : ℕ) :
    (d ∣ 2 * n ∧ d + 1 ∣ 2 * n) ↔ triangular d ∣ n := by
  have hcop : d.Coprime (d + 1) :=
    Nat.coprime_self_add_right.mpr (Nat.coprime_one_right d)
  constructor
  · intro ⟨h1, h2⟩
    have hp := hcop.mul_dvd_of_dvd_of_dvd h1 h2
    rw [← twice_triangular] at hp
    exact Nat.dvd_of_mul_dvd_mul_left (by decide) hp
  · intro ht
    have hp : 2 * triangular d ∣ 2 * n := Nat.mul_dvd_mul_left 2 ht
    rw [twice_triangular] at hp
    exact ⟨(dvd_mul_right _ _).trans hp, (dvd_mul_left _ _).trans hp⟩

theorem main : PowerSeries.mk a = lambert := by
  ext n
  simp only [PowerSeries.coeff_mk, a, lambert]
  simp_rw [divisor_iff]
  by_cases hn : n = 0
  · subst n
    rfl
  · symm
    apply Finset.sum_subset
    · intro d hd
      simp only [mem_Icc] at hd ⊢
      omega
    · intro d hd hnot
      apply if_neg
      intro hdiv
      have hdn := (triangular_ge d (by simp only [mem_Icc] at hd; omega)).trans
        (Nat.le_of_dvd (by omega) hdiv)
      exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, hdn⟩)

end OpenMath.A069972

theorem OMA.solution : type_of% @OMA.S_oeis_a069972.main := OpenMath.A069972.main
