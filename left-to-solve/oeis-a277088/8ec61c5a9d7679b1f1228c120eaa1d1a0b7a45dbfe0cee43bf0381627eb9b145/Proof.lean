import OMAStatements.S_oeis_a277088
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! A counterexample to both formulas for the Pisot sequence L(5,12), OEIS A277088. -/

namespace OpenMath.A277088

/-- The literal natural-number ceiling recurrence. -/
def a : ℕ → ℕ
  | 0 => 5
  | 1 => 12
  | n + 2 => (a (n + 1) ^ 2 + a n - 1) / a n

private def step (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.2, (p.2 ^ 2 + p.1 - 1) / p.1)

private def state (n : ℕ) : ℕ × ℕ := Nat.rec (5, 12) (fun _ p => step p) n

private theorem state_spec (n : ℕ) : state n = (a n, a (n + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change step (state n) = (a (n + 1), a (n + 2))
      rw [ih]
      rfl

private def predicted (f : ℕ → ℕ) (n : ℕ) : ℤ :=
  3 * (f (n - 1) : ℤ) - 2 * (f (n - 2) : ℤ) + 2 * (f (n - 3) : ℤ) -
    (f (n - 4) : ℤ) + (f (n - 6) : ℤ) - (f (n - 7) : ℤ) - (f (n - 9) : ℤ)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem state_witness :
    ((state 558).1 : ℤ) = predicted (fun n => (state n).1) 558 + 1 := by
  decide +kernel

theorem witness : (a 558 : ℤ) = predicted a 558 + 1 := by
  simpa only [state_spec] using state_witness

theorem recurrence_false :
    ¬ (∀ n : ℕ, 9 ≤ n → (a n : ℤ) =
      3 * (a (n - 1) : ℤ) - 2 * (a (n - 2) : ℤ) + 2 * (a (n - 3) : ℤ) -
        (a (n - 4) : ℤ) + (a (n - 6) : ℤ) - (a (n - 7) : ℤ) - (a (n - 9) : ℤ)) := by
  intro h
  have eq := h 558 (by decide)
  have neq := witness
  unfold predicted at neq
  omega

open PowerSeries in
theorem coefficient_witness :
    coeff (R := ℤ) 558
      ((1 - X) * (1 - 2 * X - 2 * X ^ 3 - X ^ 4 - X ^ 5 - 2 * X ^ 6 - X ^ 7 - X ^ 8) *
        mk (fun n => (a n : ℤ))) = 1 := by
  have hden :
      ((1 - X) * (1 - 2 * X - 2 * X ^ 3 - X ^ 4 - X ^ 5 - 2 * X ^ 6 - X ^ 7 - X ^ 8) : ℤ⟦X⟧) =
        1 - C 3 * X ^ 1 + C 2 * X ^ 2 - C 2 * X ^ 3 + X ^ 4 - X ^ 6 + X ^ 7 + X ^ 9 := by
    simp
    ring
  rw [hden]
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk,
    if_pos (by decide : 1 ≤ 558), if_pos (by decide : 2 ≤ 558), if_pos (by decide : 3 ≤ 558),
    if_pos (by decide : 4 ≤ 558), if_pos (by decide : 6 ≤ 558), if_pos (by decide : 7 ≤ 558),
    if_pos (by decide : 9 ≤ 558)]
  change (a 558 : ℤ) - 3 * (a 557 : ℤ) + 2 * (a 556 : ℤ) - 2 * (a 555 : ℤ) +
    (a 554 : ℤ) - (a 552 : ℤ) + (a 551 : ℤ) + (a 549 : ℤ) = 1
  have h : (a 558 : ℤ) = 3 * (a 557 : ℤ) - 2 * (a 556 : ℤ) + 2 * (a 555 : ℤ) -
      (a 554 : ℤ) + (a 552 : ℤ) - (a 551 : ℤ) - (a 549 : ℤ) + 1 := witness
  omega

open PowerSeries in
theorem generating_function_false :
    ¬ ((1 - X) * (1 - 2 * X - 2 * X ^ 3 - X ^ 4 - X ^ 5 - 2 * X ^ 6 - X ^ 7 - X ^ 8) *
      PowerSeries.mk (fun n => (a n : ℤ)) =
        5 - 3 * X + 3 * X ^ 2 - 2 * X ^ 3 + X ^ 5 - 3 * X ^ 6 - X ^ 7 - 2 * X ^ 8) := by
  intro h
  have hc := congrArg (coeff (R := ℤ) 558) h
  have hnum : (5 - 3 * X + 3 * X ^ 2 - 2 * X ^ 3 + X ^ 5 - 3 * X ^ 6 - X ^ 7 - 2 * X ^ 8 : ℤ⟦X⟧) =
      C 5 - C 3 * X ^ 1 + C 3 * X ^ 2 - C 2 * X ^ 3 + X ^ 5 - C 3 * X ^ 6 - X ^ 7 - C 2 * X ^ 8 := by
    simp
  rw [coefficient_witness, hnum] at hc
  simp only [map_add, map_sub, coeff_C_mul, coeff_C, coeff_X_pow] at hc
  norm_num at hc

open PowerSeries in
theorem main :
    ¬ ((∀ n : ℕ, 9 ≤ n → (a n : ℤ) =
      3 * (a (n - 1) : ℤ) - 2 * (a (n - 2) : ℤ) + 2 * (a (n - 3) : ℤ) -
        (a (n - 4) : ℤ) + (a (n - 6) : ℤ) - (a (n - 7) : ℤ) - (a (n - 9) : ℤ)) ∧
    ((1 - X) * (1 - 2 * X - 2 * X ^ 3 - X ^ 4 - X ^ 5 - 2 * X ^ 6 - X ^ 7 - X ^ 8) *
      PowerSeries.mk (fun n => (a n : ℤ)) =
        5 - 3 * X + 3 * X ^ 2 - 2 * X ^ 3 + X ^ 5 - 3 * X ^ 6 - X ^ 7 - 2 * X ^ 8)) :=
  fun h => recurrence_false h.1

end OpenMath.A277088

private theorem sameA : OMA.S_oeis_a277088.a = OpenMath.A277088.a := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 2
      · interval_cases n <;> rfl
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      change (OMA.S_oeis_a277088.a (k + 1) ^ 2 + OMA.S_oeis_a277088.a k - 1) /
          OMA.S_oeis_a277088.a k =
        (OpenMath.A277088.a (k + 1) ^ 2 + OpenMath.A277088.a k - 1) /
          OpenMath.A277088.a k
      rw [ih (k + 1) (by omega), ih k (by omega)]

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a277088.main) := by
  rw [sameA]
  exact OpenMath.A277088.main
