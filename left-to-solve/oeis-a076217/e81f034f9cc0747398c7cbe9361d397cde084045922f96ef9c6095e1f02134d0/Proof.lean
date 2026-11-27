import OMAStatements.S_oeis_a076217
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OpenMath.A076217

open OMA.S_oeis_a076217

private theorem rise {n : ℕ} (h : a n < (n + 1 : ℕ)) :
    a (n + 1) = a n + (n + 1 : ℕ) := by
  rw [a, Int.sign_eq_one_of_pos (by omega), mul_one]

private theorem fall {n : ℕ} (h : (n + 1 : ℕ) < a n) :
    a (n + 1) = a n - (n + 1 : ℕ) := by
  rw [a, Int.sign_eq_neg_one_of_neg (by omega), mul_neg_one, sub_eq_add_neg]

private theorem equal {n : ℕ} (h : a n = (n + 1 : ℕ)) :
    a (n + 1) = (n + 1 : ℕ) := by
  rw [a, h, sub_self, Int.sign_zero, mul_zero, add_zero]

private theorem block {t : ℕ} (ha : a t = t) (r : ℕ) (hr : r < t) :
    a (t + 2 * r) = (t : ℤ) - r ∧ a (t + 2 * r + 1) = 2 * (t : ℤ) + r + 1 := by
  induction r with
  | zero =>
    have hu := rise (n := t) (by omega)
    simpa using And.intro (show a t = (t : ℤ) - 0 by simpa using ha)
      (show a (t + 1) = 2 * (t : ℤ) + 0 + 1 by omega)
  | succ r ih =>
    obtain ⟨_, hhigh⟩ := ih (by omega)
    have hf := fall (n := t + 2 * r + 1) (by omega)
    have hlow : a (t + 2 * (r + 1)) = (t : ℤ) - (r + 1 : ℕ) := by
      rw [show t + 2 * (r + 1) = t + 2 * r + 1 + 1 by omega, hf]
      omega
    have hu := rise (n := t + 2 * (r + 1)) (by omega)
    exact ⟨hlow, by omega⟩

private theorem reset {t : ℕ} (ht : 0 < t) (ha : a t = t) : a (3 * t) = (3 * t : ℕ) := by
  have hlast := (block ha (t - 1) (by omega)).2
  have hlast' : a (3 * t - 1) = (3 * t : ℕ) := by
    rw [show 3 * t - 1 = t + 2 * (t - 1) + 1 by omega, hlast]
    omega
  have hnext := equal (n := 3 * t - 1) (by omega)
  rwa [show 3 * t - 1 + 1 = 3 * t by omega] at hnext

private theorem powers (k : ℕ) : a (3 ^ k) = (3 ^ k : ℕ) := by
  induction k with
  | zero => decide
  | succ k ih => simpa [pow_succ, mul_comm] using reset (Nat.pow_pos (by decide)) ih

/-- The residual of Barker's conjectured recurrence. -/
def residual (n : ℕ) : ℤ := a n + a (n - 1) - a (n - 2) - a (n - 3)

private theorem interior {t n : ℕ} (ha : a t = t)
    (hnlo : t + 3 ≤ n) (hnhi : n < 3 * t) : residual n = 0 := by
  let r := (n - t - 3) / 2
  have hr : r < t := by omega
  have hr' : r + 1 < t := by omega
  obtain ⟨hl, hh⟩ := block ha r hr
  obtain ⟨hl', hh'⟩ := block ha (r + 1) hr'
  have hpos : n = t + 2 * r + 3 ∨ n = t + 2 * r + 4 := by omega
  rcases hpos with he | ho
  · unfold residual
    rw [show n = t + 2 * (r + 1) + 1 by omega, hh',
      show t + 2 * (r + 1) + 1 - 1 = t + 2 * (r + 1) by omega, hl',
      show t + 2 * (r + 1) + 1 - 2 = t + 2 * r + 1 by omega, hh,
      show t + 2 * (r + 1) + 1 - 3 = t + 2 * r by omega, hl]
    omega
  · have hr'' : r + 2 < t := by omega
    have hl'' := (block ha (r + 2) hr'').1
    unfold residual
    rw [show n = t + 2 * (r + 2) by omega, hl'',
      show t + 2 * (r + 2) - 1 = t + 2 * (r + 1) + 1 by omega, hh',
      show t + 2 * (r + 2) - 2 = t + 2 * (r + 1) by omega, hl',
      show t + 2 * (r + 2) - 3 = t + 2 * r + 1 by omega, hh]
    omega

private theorem boundary {t : ℕ} (ht : 2 ≤ t) (ha : a t = t) :
    residual (3 * t) = (3 * t : ℕ) ∧ residual (3 * t + 1) = (6 * t : ℕ) ∧
      residual (3 * t + 2) = (3 * t : ℕ) := by
  obtain ⟨hl, hh⟩ := block ha (t - 1) (by omega)
  have hh' := (block ha (t - 2) (by omega)).2
  have hl1 : a (3 * t - 2) = 1 := by
    rw [show 3 * t - 2 = t + 2 * (t - 1) by omega, hl]
    omega
  have hh1 : a (3 * t - 1) = (3 * t : ℕ) := by
    rw [show 3 * t - 1 = t + 2 * (t - 1) + 1 by omega, hh]
    omega
  have hh2 : a (3 * t - 3) = (3 * t : ℕ) - 1 := by
    rw [show 3 * t - 3 = t + 2 * (t - 2) + 1 by omega, hh']
    omega
  have hreset := reset (by omega) ha
  have h1 : a (3 * t + 1) = (6 * t : ℕ) + 1 := by
    have h := (block hreset 0 (by omega)).2
    simp only [mul_zero, add_zero, Nat.cast_mul, Nat.cast_ofNat] at h ⊢
    omega
  have h2 : a (3 * t + 2) = (3 * t : ℕ) - 1 := by
    have h := (block hreset 1 (by omega)).1
    simpa using h
  constructor
  · simp only [residual, hreset, hl1, hh1, hh2]
    omega
  constructor
  · rw [residual, h1, show 3 * t + 1 - 1 = 3 * t by omega, hreset,
      show 3 * t + 1 - 2 = 3 * t - 1 by omega, hh1,
      show 3 * t + 1 - 3 = 3 * t - 2 by omega, hl1]
    omega
  · rw [residual, h2, show 3 * t + 2 - 1 = 3 * t + 1 by omega, h1,
      show 3 * t + 2 - 2 = 3 * t by omega, hreset,
      show 3 * t + 2 - 3 = 3 * t - 1 by omega, hh1]
    omega

private theorem no_boundary (n : ℕ) (hn : 5 < n)
    (h : ¬ ∃ k : ℕ, 2 ≤ k ∧ 3 ^ k ≤ n ∧ n < 3 ^ k + 3) : residual n = 0 := by
  set k := Nat.log 3 n
  have hlo : 3 ^ k ≤ n := Nat.pow_log_le_self 3 (by omega)
  have hhi : n < 3 * 3 ^ k := by
    simpa [pow_succ, mul_comm] using Nat.lt_pow_succ_log_self (b := 3) (by decide) n
  have hgap : 3 ^ k + 3 ≤ n := by
    by_contra! hsmall
    have hk : 2 ≤ k := by
      by_contra! hk
      interval_cases k <;> norm_num at hsmall <;> omega
    exact h ⟨k, hk, hlo, hsmall⟩
  exact interior (powers k) hgap hhi

private theorem at_boundary (n k : ℕ) (hk : 2 ≤ k) (hlo : 3 ^ k ≤ n)
    (hhi : n < 3 ^ k + 3) : residual n ≠ 0 := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : 1 ≤ j := by omega
  have hpow : 2 ≤ 3 ^ j := by
    calc
      2 ≤ 3 ^ (1 : ℕ) := by decide
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by decide) hj
  have h := boundary hpow (powers j)
  simp only [pow_succ, mul_comm _ (3 : ℕ)] at hlo hhi
  obtain hn | hn | hn : n = 3 * 3 ^ j ∨ n = 3 * 3 ^ j + 1 ∨ n = 3 * 3 ^ j + 2 := by omega
  · rw [hn, h.1]
    omega
  · rw [hn, h.2.1]
    omega
  · rw [hn, h.2.2]
    omega

/-- McEachen's proposed exceptional indices are exactly the recurrence failures. -/
theorem main (n : ℕ) (hn : 5 < n) :
    (a n = -a (n - 1) + a (n - 2) + a (n - 3)) ↔
      ¬ ∃ k : ℕ, 2 ≤ k ∧ 3 ^ k ≤ n ∧ n < 3 ^ k + 3 := by
  constructor
  · intro h ⟨k, hk, hlo, hhi⟩
    apply at_boundary n k hk hlo hhi
    unfold residual
    omega
  · intro h
    have hzero := no_boundary n hn h
    unfold residual at hzero
    omega

end OpenMath.A076217


theorem OMA.solution : type_of% @OMA.S_oeis_a076217.main := OpenMath.A076217.main
