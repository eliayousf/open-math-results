import OMAStatements.S_oeis_a018918
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! The recurrence and generating function for the strict Pisot sequence in OEIS A018918. -/

namespace OpenMath.A018918

/-- Strict rounding selects the largest integer strictly below the quotient. -/
def a : ℕ → ℕ
  | 0 => 3
  | 1 => 6
  | n + 2 => (a (n + 1) ^ 2 - 1) / a n

private def b : ℕ → ℤ
  | 0 => 3
  | 1 => 6
  | 2 => 11
  | 3 => 20
  | n + 4 => 3 * b (n + 3) - 3 * b (n + 2) + 2 * b (n + 1) - b n

private theorem b_step (n : ℕ) :
    b (n + 4) = 3 * b (n + 3) - 3 * b (n + 2) + 2 * b (n + 1) - b n := rfl

private def c (n : ℕ) : ℤ := b n + 1

private theorem c_cubic (n : ℕ) :
    c (n + 3) = 2 * c (n + 2) - c (n + 1) + c n := by
  induction n with
  | zero => decide
  | succ n ih =>
      have step : c (n + 4) =
          3 * c (n + 3) - 3 * c (n + 2) + 2 * c (n + 1) - c n := by
        unfold c
        rw [b_step n]
        ring
      change c (n + 4) = 2 * c (n + 3) - c (n + 2) + c (n + 1)
      omega

private theorem c_step (n : ℕ) :
    c (n + 4) = c (n + 3) + c (n + 2) + c n := by
  have h₀ := c_cubic n
  have h₁ : c (n + 4) = 2 * c (n + 3) - c (n + 2) + c (n + 1) := c_cubic (n + 1)
  omega

private theorem c_lower (n : ℕ) : 4 ≤ c n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 4
      · interval_cases n <;> decide
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have h₀ := ih k (by omega)
      have h₂ := ih (k + 2) (by omega)
      have h₃ := ih (k + 3) (by omega)
      rw [c_step k]
      omega

private theorem c_ratios (n : ℕ) (hn : 4 ≤ n) :
    7 * c n ≤ 4 * c (n + 1) ∧ 25 * c (n + 1) ≤ 44 * c n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 8
      · interval_cases n <;> decide
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have h₀ := ih k (by omega) (by omega)
      have h₂ := ih (k + 2) (by omega) (by omega)
      have h₃ := ih (k + 3) (by omega) (by omega)
      have ha := c_step k
      have hb := c_step (k + 1)
      simp only [Nat.add_assoc, Nat.reduceAdd] at h₂ h₃ hb ⊢
      exact ⟨by omega, by omega⟩

private def D (n : ℕ) : ℤ := c (n + 1) ^ 2 - c n * c (n + 2)

private theorem D_cubic (n : ℕ) :
    D (n + 3) = D (n + 2) - 2 * D (n + 1) + D n := by
  unfold D
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [show c (n + 5) = 2 * c (n + 4) - c (n + 3) + c (n + 2) from c_cubic (n + 2),
    show c (n + 4) = 2 * c (n + 3) - c (n + 2) + c (n + 1) from c_cubic (n + 1),
    c_cubic n]
  ring

private theorem D_step (n : ℕ) : D (n + 4) = D n - D (n + 1) - D (n + 2) := by
  have h₀ := D_cubic n
  have h₁ : D (n + 4) = D (n + 3) - 2 * D (n + 2) + D (n + 1) := D_cubic (n + 1)
  omega

private theorem D_bounds (n : ℕ) (hn : 4 ≤ n) :
    -(3 * c n) ≤ 10 * D n ∧ 10 * D n ≤ 3 * c n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 8
      · interval_cases n <;> decide
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have h₀ := ih k (by omega) (by omega)
      have h₁ := ih (k + 1) (by omega) (by omega)
      have h₂ := ih (k + 2) (by omega) (by omega)
      have grow₁ := (c_ratios (k + 1) (by omega)).1
      have grow₂ := (c_ratios (k + 2) (by omega)).1
      have positive := c_lower (k + 1)
      have hc := c_step k
      have hd := D_step k
      simp only [Nat.add_assoc, Nat.reduceAdd] at grow₁ grow₂
      exact ⟨by omega, by omega⟩

private def d (n : ℕ) : ℤ := b (n + 1) ^ 2 - b n * b (n + 2)

private theorem d_bounds (n : ℕ) : 0 < d n ∧ d n ≤ b n := by
  by_cases h : n < 4
  · interval_cases n <;> decide
  have hD := D_bounds n (by omega)
  have hr0 := c_ratios n (by omega)
  have hr1 := c_ratios (n + 1) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hr1
  have hd : d n = D n + c n + c (n + 2) - 2 * c (n + 1) := by
    unfold d D c
    ring
  have hlo : 13 * c n ≤ 50 * d n := by omega
  have hhi : 25 * d n ≤ 22 * c n := by omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hc : 12 ≤ c (k + 4) := by
    rw [c_step k]
    have h₀ := c_lower k
    have h₂ := c_lower (k + 2)
    have h₃ := c_lower (k + 3)
    omega
  have hf : c (k + 4) = b (k + 4) + 1 := rfl
  exact ⟨by omega, by omega⟩

private theorem b_pos (n : ℕ) : 0 < b n := by
  have h : 4 ≤ b n + 1 := c_lower n
  omega

private theorem a_eq_b (n : ℕ) : (a n : ℤ) = b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 2
      · interval_cases n <;> rfl
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      have ha : 0 < a (k + 1) := by
        exact_mod_cast (show (0 : ℤ) < (a (k + 1) : ℤ) by
          rw [ih (k + 1) (by omega)]
          exact b_pos _)
      have hpow : 1 ≤ a (k + 1)^2 := Nat.succ_le_of_lt (pow_pos ha _)
      change (((a (k + 1) ^ 2 - 1) / a k : ℕ) : ℤ) = b (k + 2)
      rw [Int.natCast_ediv, Int.natCast_sub hpow, Int.natCast_pow,
        ih (k + 1) (by omega), ih k (by omega)]
      have hb := b_pos k
      obtain ⟨hlo, hhi⟩ := d_bounds k
      unfold d at hlo hhi
      apply (Int.ediv_eq_iff_of_pos hb).2
      rw [mul_comm (b (k + 2))]
      omega

theorem linear_recurrence (n : ℕ) :
    (a (n + 4) : ℤ) = 3 * (a (n + 3) : ℤ) - 3 * (a (n + 2) : ℤ) +
      2 * (a (n + 1) : ℤ) - (a n : ℤ) := by
  simpa only [a_eq_b] using b_step n

open PowerSeries in
theorem generating_function :
    (1 - X) * (1 - 2 * X + X ^ 2 - X ^ 3) * mk (fun n => (a n : ℤ)) =
      (3 - 3 * X + 2 * X ^ 2 - X ^ 3 : ℤ⟦X⟧) := by
  simp only [a_eq_b]
  have hden : ((1 - X) * (1 - 2 * X + X ^ 2 - X ^ 3) : ℤ⟦X⟧) =
      1 - C 3 * X ^ 1 + C 3 * X ^ 2 - C 2 * X ^ 3 + X ^ 4 := by
    simp
    ring
  have hnum : (3 - 3 * X + 2 * X ^ 2 - X ^ 3 : ℤ⟦X⟧) =
      C 3 - C 3 * X ^ 1 + C 2 * X ^ 2 - X ^ 3 := by simp
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
  by_cases h : n < 4
  · interval_cases n <;> norm_num [b]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [if_pos (show 1 ≤ k + 4 by omega), if_pos (show 2 ≤ k + 4 by omega),
    if_pos (show 3 ≤ k + 4 by omega), if_pos (show 4 ≤ k + 4 by omega),
    if_neg (show k + 4 ≠ 0 by omega), if_neg (show k + 4 ≠ 1 by omega),
    if_neg (show k + 4 ≠ 2 by omega), if_neg (show k + 4 ≠ 3 by omega)]
  change b (k + 4) - 3 * b (k + 3) + 3 * b (k + 2) - 2 * b (k + 1) + b k = _
  have hb := b_step k
  omega

open PowerSeries in
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) +
      2 * (a (n - 3) : ℤ) - (a (n - 4) : ℤ)) ∧
    ((1 - X) * (1 - 2 * X + X ^ 2 - X ^ 3) * PowerSeries.mk (fun n => (a n : ℤ)) =
      3 - 3 * X + 2 * X ^ 2 - X ^ 3) := by
  refine ⟨?_, generating_function⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  exact linear_recurrence k

end OpenMath.A018918

private theorem sameA : OMA.S_oeis_a018918.a = OpenMath.A018918.a := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 2
      · interval_cases n <;> rfl
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      change (OMA.S_oeis_a018918.a (k + 1) ^ 2 - 1) / OMA.S_oeis_a018918.a k =
        (OpenMath.A018918.a (k + 1) ^ 2 - 1) / OpenMath.A018918.a k
      rw [ih (k + 1) (by omega), ih k (by omega)]

theorem OMA.solution : type_of% @OMA.S_oeis_a018918.main := by
  rw [sameA]
  exact OpenMath.A018918.main

