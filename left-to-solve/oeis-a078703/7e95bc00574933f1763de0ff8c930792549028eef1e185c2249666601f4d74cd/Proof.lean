import OMAStatements.S_oeis_a078703
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Linarith

namespace OpenMath.A078703

open Finset

open OMA.S_oeis_a078703 (a lambert squareWays rows)

private theorem shape (j k : ℕ) (hj : 0 < j) :
    (k + j) ^ 2 = (j ^ 2 + (2 * j - 1) * k) + k * (k + 1) := by
  have h : (2 * j - 1) * k + k = 2 * j * k := by
    calc
      _ = (2 * j - 1) * k + 1 * k := by rw [one_mul]
      _ = _ := by rw [← Nat.add_mul, show 2 * j - 1 + 1 = 2 * j by omega]
  nlinarith only [h]

private theorem forward (n x k : ℕ) (hx : 0 < x) (hn : x ^ 2 = n + k * (k + 1)) :
    ∃ j : ℕ, 0 < j ∧ x = k + j ∧ n = j ^ 2 + (2 * j - 1) * k := by
  have hkx : k < x := by
    by_contra! h
    have hm := Nat.pow_le_pow_left h 2
    have hp := Nat.mul_le_mul_left 1 h
    nlinarith only [hm, hp, hn, hx]
  let j := x - k
  have hj : 0 < j := by dsimp [j]; omega
  have he : x = k + j := by dsimp [j]; omega
  refine ⟨j, hj, he, ?_⟩
  have hh := shape j k hj
  rw [← he] at hh
  omega

private theorem source_bounds (n x k : ℕ) (hx : 0 < x)
    (he : x ^ 2 = n + k * (k + 1)) : x ≤ n ∧ k < n := by
  obtain ⟨j, hj, hsum, hn⟩ := forward n x k hx he
  have hmul : k ≤ (2 * j - 1) * k := by
    simpa only [one_mul] using Nat.mul_le_mul_right k (show 1 ≤ 2 * j - 1 by omega)
  have hsq : j ≤ j ^ 2 := by
    simpa only [one_mul, pow_two] using Nat.mul_le_mul_right j (show 1 ≤ j by omega)
  omega

private theorem membership (n x k : ℕ) :
    (x,k) ∈ squareWays n ↔ 0 < x ∧ x ≤ n ∧ k < n ∧ x ^ 2 = n + k * (k + 1) := by
  simp only [squareWays, mem_filter, mem_product, mem_Icc, mem_range]
  omega

private theorem row_membership (n j : ℕ) :
    j ∈ rows n ↔ 0 < j ∧ j ≤ n ∧ j ^ 2 ≤ n ∧ (2 * j - 1) ∣ n - j ^ 2 := by
  simp only [rows, mem_filter, mem_Icc]
  omega

private theorem count (n : ℕ) : a n = (rows n).card := by
  unfold a
  refine Finset.card_bij (fun p _ => p.1 - p.2) ?_ ?_ ?_
  · rintro ⟨x,k⟩ hm
    obtain ⟨hx, hxn, _, he⟩ := (membership n x k).mp hm
    obtain ⟨j, hj, hsum, hr⟩ := forward n x k hx he
    have hsub : x - k = j := by omega
    change x - k ∈ rows n
    rw [hsub, row_membership]
    exact ⟨hj, by omega, by omega, ⟨k, by omega⟩⟩
  · rintro ⟨x,k⟩ hm ⟨y,l⟩ hm' hd
    obtain ⟨hx, _, _, he⟩ := (membership n x k).mp hm
    obtain ⟨hy, _, _, he'⟩ := (membership n y l).mp hm'
    obtain ⟨j, hj, hs, hn⟩ := forward n x k hx he
    obtain ⟨jj, _, hs', hn'⟩ := forward n y l hy he'
    change x - k = y - l at hd
    have hjj : jj = j := by omega
    subst jj
    have hk : k = l := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * j - 1) (by omega)
    have hxy : x = y := by omega
    exact Prod.ext hxy hk
  · intro j hj
    obtain ⟨hj1, _, hjn, k, hk⟩ := (row_membership n j).mp hj
    have hn : n = j ^ 2 + (2 * j - 1) * k := by omega
    have hh := shape j k hj1
    rw [← hn] at hh
    have hx : 0 < k + j := by omega
    obtain ⟨hxn, hkn⟩ := source_bounds n (k+j) k hx hh
    exact ⟨(k+j,k), (membership n (k+j) k).mpr ⟨hx, hxn, hkn, hh⟩, by
      change k+j-k=j
      omega⟩

theorem main : PowerSeries.mk a = lambert := by
  ext n
  simp only [PowerSeries.coeff_mk, lambert]
  exact count n

end OpenMath.A078703

theorem OMA.solution : type_of% @OMA.S_oeis_a078703.main := OpenMath.A078703.main
