import OMAStatements.S_oeis_a018917
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! The strict generalized Pisot sequence T(3,5), OEIS A018917. -/

namespace OpenMath.A018917

/-- Greatest integer strictly below the square quotient at each step. -/
def a : ℕ → ℕ
  | 0 => 3
  | 1 => 5
  | n + 2 => (a (n + 1) ^ 2 - 1) / a n

/-- Padovan numbers with the initial values of OEIS A000931. -/
def padovan : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | n + 3 => padovan (n + 1) + padovan n

private def b : ℕ → ℤ
  | 0 => 3
  | 1 => 5
  | 2 => 8
  | 3 => 12
  | n + 4 => b (n + 3) + b (n + 2) - b n

private theorem b_step (n : ℕ) :
    b (n + 4) = b (n + 3) + b (n + 2) - b n := rfl

private theorem b_affine (n : ℕ) : b (n + 3) = b (n + 1) + b n + 4 := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [Nat.add_assoc, Nat.reduceAdd]
      have hb := b_step n
      omega

private theorem b_pos (n : ℕ) : 0 < b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 3
      · interval_cases n <;> norm_num [b]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      rw [b_affine k]
      have h0 := ih k (by omega)
      have h1 := ih (k + 1) (by omega)
      omega

private def c (n : ℕ) : ℤ := b n + 4

private theorem c_pos (n : ℕ) : 0 < c n := by
  have hb := b_pos n
  unfold c
  omega

private theorem c_step (n : ℕ) : c (n + 3) = c (n + 1) + c n := by
  unfold c
  rw [b_affine]
  omega

private theorem c_ratios (n : ℕ) (hn : 4 ≤ n) :
    33 * c n ≤ 25 * c (n + 1) ∧ 3 * c (n + 1) ≤ 4 * c n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 7
      · interval_cases n <;> norm_num [c, b]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      obtain ⟨h0lo, h0hi⟩ := ih k (by omega) (by omega)
      obtain ⟨h1lo, h1hi⟩ := ih (k + 1) (by omega) (by omega)
      have hs := c_step k
      have ht := c_step (k + 1)
      simp only [Nat.add_assoc, Nat.reduceAdd] at h1lo h1hi ht ⊢
      exact ⟨by omega, by omega⟩

private theorem c_large (n : ℕ) (hn : 5 ≤ n) : 28 ≤ c n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
      have hr := (c_ratios n (by omega)).1
      omega

private def err (n : ℕ) : ℤ := c (n + 1) ^ 2 - c n * c (n + 2)

private theorem err_step (n : ℕ) : err (n + 3) = err n - err (n + 2) := by
  have h3 := c_step n
  have h4 := c_step (n + 1)
  have h5 := c_step (n + 2)
  unfold err
  simp only [Nat.add_assoc, Nat.reduceAdd] at h4 h5 ⊢
  rw [h5, h4, h3]
  ring

private theorem err_five (n : ℕ) : err (n + 5) = err n - err (n + 1) := by
  have h0 := err_step n
  have h1 := err_step (n + 1)
  have h2 := err_step (n + 2)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h2
  omega

private theorem err_bound (n : ℕ) (hn : 4 ≤ n) :
    -c n ≤ 3 * err n ∧ 3 * err n ≤ c n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 9
      · interval_cases n <;> norm_num [err, c, b]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      obtain ⟨h0lo, h0hi⟩ := ih k (by omega) (by omega)
      obtain ⟨h1lo, h1hi⟩ := ih (k + 1) (by omega) (by omega)
      have hs := err_five k
      have hc3 := c_step k
      have hc5 := c_step (k + 2)
      simp only [Nat.add_assoc, Nat.reduceAdd] at hc5
      have hp := c_pos (k + 2)
      exact ⟨by omega, by omega⟩

private def d (n : ℕ) : ℤ := b (n + 1) ^ 2 - b n * b (n + 2)

private theorem error_relation (n : ℕ) :
    d n = err n + 4 * (c n + c (n + 2) - 2 * c (n + 1)) := by
  unfold d err c
  ring

private theorem d_bounds (n : ℕ) : 0 < d n ∧ d n ≤ b n := by
  by_cases h : n < 5
  · interval_cases n <;> norm_num [d, b]
  have h0 := c_ratios n (by omega)
  have h1 := c_ratios (n + 1) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1
  obtain ⟨hdlo, hdhi⟩ := err_bound n (by omega)
  have hr := error_relation n
  have hlarge := c_large n (by omega)
  have hb : c n = b n + 4 := rfl
  exact ⟨by omega, by omega⟩

private theorem a_eq_b (n : ℕ) : (a n : ℤ) = b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 2
      · interval_cases n <;> rfl
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      have hi := ih (k + 1) (by omega)
      have hb := b_pos (k + 1)
      have ha : 0 < a (k + 1) := by omega
      have hpow : 1 ≤ a (k + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
      change (((a (k + 1) ^ 2 - 1) / a k : ℕ) : ℤ) = b (k + 2)
      rw [Int.natCast_ediv, Int.natCast_sub hpow, Int.natCast_pow,
        hi, ih k (by omega)]
      obtain ⟨hlo, hhi⟩ := d_bounds k
      unfold d at hlo hhi
      apply (Int.ediv_eq_iff_of_pos (b_pos k)).2
      rw [mul_comm (b (k + 2))]
      exact ⟨by omega, by omega⟩

theorem linear_recurrence (n : ℕ) :
    (a (n + 4) : ℤ) = (a (n + 3) : ℤ) + (a (n + 2) : ℤ) - (a n : ℤ) := by
  simp only [a_eq_b]
  exact b_step n

private theorem diff_step (n : ℕ) :
    b (n + 4) - b (n + 3) = (b (n + 2) - b (n + 1)) + (b (n + 1) - b n) := by
  have hs := b_affine n
  have ht := b_affine (n + 1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at ht
  omega

private theorem b_padovan (n : ℕ) : b (n + 1) - b n = (padovan (n + 9) : ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 3
      · interval_cases n <;> norm_num [b, padovan]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have h0 := ih k (by omega)
      have h1 := ih (k + 1) (by omega)
      have hs : padovan (k + 12) = padovan (k + 10) + padovan (k + 9) := rfl
      simp only [Nat.add_assoc, Nat.reduceAdd] at h1 ⊢
      rw [diff_step k, h1, h0, hs, Int.natCast_add]

theorem padovan_identity (n : ℕ) : a (n + 1) = a n + padovan (n + 9) := by
  have hb := b_padovan n
  have h0 := a_eq_b n
  have h1 := a_eq_b (n + 1)
  omega

open PowerSeries in
theorem generating_function :
    (1 - X) * (1 - X ^ 2 - X ^ 3) *
      mk (fun n => (a n : ℤ)) = (3 + 2 * X - X ^ 3 : ℤ⟦X⟧) := by
  simp only [a_eq_b]
  have hden : ((1 - X) * (1 - X ^ 2 - X ^ 3) : ℤ⟦X⟧) = 1 - X ^ 1 - X ^ 2 + X ^ 4 := by
    ring
  have hnum : (3 + 2 * X - X ^ 3 : ℤ⟦X⟧) = C 3 + C 2 * X ^ 1 - X ^ 3 := by simp
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
  by_cases h : n < 4
  · interval_cases n <;> norm_num [b]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [if_pos (show 1 ≤ k + 4 by omega), if_pos (show 2 ≤ k + 4 by omega),
    if_pos (show 4 ≤ k + 4 by omega),
    if_neg (show k + 4 ≠ 0 by omega), if_neg (show k + 4 ≠ 1 by omega),
    if_neg (show k + 4 ≠ 3 by omega)]
  change b (k + 4) - b (k + 3) - b (k + 2) + b k = _
  have hb := b_step k
  omega

open PowerSeries in
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = (a (n - 1) : ℤ) + (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧
    ((1 - X) * (1 - X ^ 2 - X ^ 3) * PowerSeries.mk (fun n => (a n : ℤ)) = 3 + 2 * X - X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → a n = a (n - 1) + padovan (n + 8)) := by
  refine ⟨?_, generating_function, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    exact linear_recurrence k
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact padovan_identity k

end OpenMath.A018917

private theorem source_a_eq : OMA.S_oeis_a018917.a = OpenMath.A018917.a := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 2
      · interval_cases n <;> rfl
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      change (OMA.S_oeis_a018917.a (k + 1) ^ 2 - 1) / OMA.S_oeis_a018917.a k =
        (OpenMath.A018917.a (k + 1) ^ 2 - 1) / OpenMath.A018917.a k
      rw [ih (k + 1) (by omega), ih k (by omega)]

private theorem source_padovan_eq : OMA.S_oeis_a018917.padovan = OpenMath.A018917.padovan := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h : n < 3
      · interval_cases n <;> rfl
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      change OMA.S_oeis_a018917.padovan (k + 1) + OMA.S_oeis_a018917.padovan k =
        OpenMath.A018917.padovan (k + 1) + OpenMath.A018917.padovan k
      rw [ih (k + 1) (by omega), ih k (by omega)]

theorem OMA.solution : type_of% @OMA.S_oeis_a018917.main := by
  rw [source_a_eq, source_padovan_eq]
  exact OpenMath.A018917.main
