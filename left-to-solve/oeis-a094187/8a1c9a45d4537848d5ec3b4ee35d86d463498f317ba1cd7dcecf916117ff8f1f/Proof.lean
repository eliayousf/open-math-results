import OMAStatements.S_oeis_a094187
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OpenMath.A094187

open Finset

open OMA.S_oeis_a094187 (moment integral oddprod a)

private theorem moment_mul (k : ℕ) :
    (1 - 2 * (k : ℚ)) * moment k = (9 / 8 : ℚ) * (64 / 81 : ℚ)^k - 1 := by
  have h : (1 - 2 * (k : ℚ)) ≠ 0 := by
    intro he
    by_cases hk : k = 0
    · subst k; norm_num at he
    · have hc : (1 : ℚ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      linarith
  rw [moment, mul_div, mul_comm (1 - 2 * (k : ℚ)), mul_div_cancel_right₀ _ h]

private theorem integral_step (n : ℕ) :
    (2 * ((n : ℚ) + 1) - 1) * integral (n + 1) - 2 * ((n : ℚ) + 1) * integral n =
      -(9 / 8 : ℚ) * (17 / 81 : ℚ) ^ (n + 1) := by
  have hpad : integral n =
      ∑ k ∈ range (n + 1 + 1), (n.choose k : ℚ) * (-1 : ℚ)^k * moment k := by
    rw [sum_range_succ]
    simp [integral]
  have hnew : integral (n + 1) =
      ∑ k ∈ range (n + 1 + 1), ((n + 1).choose k : ℚ) * (-1 : ℚ)^k * moment k := rfl
  rw [hnew, hpad]
  simp only [mul_sum, ← sum_sub_distrib]
  calc
    _ = ∑ k ∈ range (n + 1 + 1),
        ((n + 1).choose k : ℚ) * (-1 : ℚ)^k * (1 - (9 / 8 : ℚ) * (64 / 81 : ℚ)^k) := by
      apply sum_congr rfl
      intro k hk
      have hnk : k ≤ n + 1 := by simpa using hk
      have hc : (n.choose k : ℚ) * ((n : ℚ) + 1) =
          ((n + 1).choose k : ℚ) * ((n : ℚ) + 1 - (k : ℚ)) := by
        have hnat := Nat.choose_mul_succ_eq n k
        have hcast := congrArg (fun z : ℕ => (z : ℚ)) hnat
        push_cast [Nat.cast_sub hnk] at hcast
        exact hcast
      calc
        _ = (((2 * ((n : ℚ) + 1) - 1) * ((n + 1).choose k : ℚ)) -
              2 * ((n.choose k : ℚ) * ((n : ℚ) + 1))) * (-1 : ℚ)^k * moment k := by ring
        _ = ((n + 1).choose k : ℚ) * (-1 : ℚ)^k *
              (-((1 - 2 * (k : ℚ)) * moment k)) := by rw [hc]; ring
        _ = _ := by rw [moment_mul]; ring
    _ = -(9 / 8 : ℚ) * (17 / 81 : ℚ) ^ (n + 1) := by
      have hb : ∑ k ∈ range (n + 1 + 1), ((n + 1).choose k : ℚ) * (-1 : ℚ)^k = 0 := by
        simpa [mul_comm] using (add_pow (-1 : ℚ) 1 (n + 1)).symm
      have hp : ∑ k ∈ range (n + 1 + 1),
          ((n + 1).choose k : ℚ) * (-(64 / 81 : ℚ))^k = (17 / 81 : ℚ)^(n + 1) := by
        have h := (add_pow (-(64 / 81 : ℚ)) 1 (n + 1)).symm
        norm_num at h ⊢
        simpa [mul_comm] using h
      simp_rw [mul_sub, mul_one]
      rw [sum_sub_distrib, hb]
      have hsum : ∑ k ∈ range (n + 1 + 1),
          ((n + 1).choose k : ℚ) * (-1 : ℚ)^k * ((9 / 8 : ℚ) * (64 / 81 : ℚ)^k) =
          (9 / 8 : ℚ) * (17 / 81 : ℚ)^(n + 1) := by
        rw [← hp, mul_sum]
        apply sum_congr rfl
        intro k _
        rw [show -(64 / 81 : ℚ) = (-1 : ℚ) * (64 / 81 : ℚ) by norm_num, mul_pow]
        ring
      rw [hsum]
      ring

private def boundary (n : ℕ) : ℚ := 17^(n + 1) * oddprod n

private theorem oddprod_step (n : ℕ) : oddprod (n + 1) = oddprod n * (2 * (n : ℚ) + 1) := by
  rw [oddprod, prod_range_succ]
  rfl

private theorem boundary_step (n : ℕ) :
    boundary (n + 1) = 17 * (2 * (n : ℚ) + 1) * boundary n := by
  unfold boundary
  rw [oddprod_step, pow_succ (17 : ℚ) (n + 1)]
  ring

private theorem a_step (n : ℕ) :
    a (n + 1) = 162 * ((n : ℚ) + 1) * a n - boundary n := by
  have hpow : (81 : ℚ)^(n+1) * (17 / 81 : ℚ)^(n+1) = 17^(n+1) := by
    rw [← mul_pow]
    norm_num
  have h := congrArg (fun q : ℚ => (8 / 9 : ℚ) * (81 : ℚ)^(n+1) * oddprod n * q)
    (integral_step n)
  have hs :
      (8 / 9 : ℚ) * (81 : ℚ)^(n+1) * oddprod n *
        (-(9 / 8 : ℚ) * (17 / 81 : ℚ)^(n + 1)) = -(17 : ℚ)^(n+1) * oddprod n := by
    calc
      _ = -((81 : ℚ)^(n+1) * (17 / 81 : ℚ)^(n+1)) * oddprod n := by ring
      _ = _ := by rw [hpow]
  rw [hs] at h
  unfold a boundary
  rw [oddprod_step]
  rw [pow_succ (81 : ℚ) n] at h ⊢
  linear_combination h

theorem main : ∀ n ≥ 3,
    a n = (196 * (n : ℚ) - 51) * a (n - 1) -
      2754 * ((n : ℚ) - 1) * (2 * (n : ℚ) - 3) * a (n - 2) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j + 2 := ⟨n-2, by omega⟩
  rw [show j+2-1=j+1 by omega, show j+2-2=j by omega]
  push_cast
  have ht := boundary_step j
  have h0 := a_step j
  have h1 := a_step (j+1)
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.reduceAdd] at h1
  linear_combination h1 - 17 * (2 * (j : ℚ) + 1) * h0 - ht

end OpenMath.A094187

theorem OMA.solution : type_of% @OMA.S_oeis_a094187.main := OpenMath.A094187.main
