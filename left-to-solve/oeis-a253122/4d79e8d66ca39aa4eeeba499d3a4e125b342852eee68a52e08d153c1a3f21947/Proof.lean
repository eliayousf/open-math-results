import OMAStatements.S_oeis_a253122
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace A253122

open OMA.S_oeis_a253122

private theorem total (k : ℕ) (x y : Bool) :
    completions k x y false + completions k x y true = 2 ^ k := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    have h0 := ih y false
    have h1 := ih y true
    cases x <;> cases y <;>
      simp [completions, median, Bool.xor, pow_succ] <;> omega

private def signed (k : ℕ) (x y : Bool) : ℤ :=
  (completions k x y false : ℤ) - completions k x y true

private theorem signed00 (k : ℕ) :
    signed (k + 1) false false = signed k false false + signed k false true := by
  simp [signed, completions, median, Bool.xor]
  omega

private theorem signed01 (k : ℕ) :
    signed (k + 1) false true = signed k true false - signed k true true := by
  simp [signed, completions, median, Bool.xor]
  omega

private theorem signed10 (k : ℕ) :
    signed (k + 1) true false = signed k false false - signed k false true := by
  simp [signed, completions, median, Bool.xor]
  omega

private theorem signed11 (k : ℕ) :
    signed (k + 1) true true = -signed k true false - signed k true true := by
  simp [signed, completions, median, Bool.xor]
  omega

private def difference (k : ℕ) : ℤ :=
  signed k false false + signed k false true + signed k true false + signed k true true

private theorem difference_next (k : ℕ) :
    difference (k + 1) = 2 * (signed k false false - signed k true true) := by
  unfold difference
  rw [signed00, signed01, signed10, signed11]
  ring

private theorem difference_step (k : ℕ) : difference (k + 2) = 2 * difference k := by
  change difference (k + 1 + 1) = _
  rw [difference_next, signed00, signed11]
  unfold difference
  ring

private theorem difference_even (k : ℕ) : difference (2 * k) = 2 ^ (k + 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, difference_step, ih]
    rw [pow_succ (2 : ℤ) (k + 2)]
    ring

private theorem difference_odd (k : ℕ) : difference (2 * k + 1) = 0 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by omega, difference_step, ih]
    norm_num

private theorem count_bridge (k : ℕ) :
    2 * (countedWords k : ℤ) = 2 ^ (k + 2) + difference k := by
  have totals (x y : Bool) :
      (completions k x y false : ℤ) + completions k x y true = (2 : ℤ) ^ k := by
    exact_mod_cast total k x y
  have h0 := totals false false
  have h1 := totals false true
  have h2 := totals true false
  have h3 := totals true true
  unfold countedWords difference signed
  push_cast
  rw [pow_add]
  norm_num
  omega

private theorem even_count (n : ℕ) (hn : 0 < n) (he : n % 2 = 0) :
    a n = 2 ^ (n / 2 + 1) + 2 ^ (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  rw [a, if_neg (by omega), show 2 * k / 2 = k by omega]
  have h := count_bridge (2 * k)
  rw [difference_even] at h
  have hnat : 2 * countedWords (2 * k) = 2 ^ (2 * k + 2) + 2 ^ (k + 2) := by
    exact_mod_cast h
  rw [pow_succ 2 (2 * k + 1), pow_succ 2 (k + 1)] at hnat
  omega

private theorem odd_count (n : ℕ) (hn : 0 < n) (ho : n % 2 = 1) : a n = 2 ^ (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  rw [a, if_neg (by omega)]
  have h := count_bridge (2 * k + 1)
  rw [difference_odd, add_zero] at h
  have hnat : 2 * countedWords (2 * k + 1) = 2 ^ (2 * k + 1 + 2) := by
    exact_mod_cast h
  rw [pow_succ 2 (2 * k + 1 + 1)] at hnat
  omega

private theorem count_step (k : ℕ) :
    (countedWords (k + 2) : ℤ) - 2 * countedWords k = 2 ^ (k + 2) := by
  have h0 := count_bridge k
  have h2 := count_bridge (k + 2)
  have hp : (2 : ℤ) ^ (k + 2 + 2) = 4 * 2 ^ (k + 2) := by
    rw [pow_add]
    ring
  rw [difference_step, hp] at h2
  omega

private theorem recurrence (k : ℕ) (hk : 0 < k) :
    (a (k + 3) : ℤ) - 2 * a (k + 2) - 2 * a (k + 1) + 4 * a k = 0 := by
  have h0 := count_step k
  have h1 := count_step (k + 1)
  have hp : (2 : ℤ) ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) := by
    rw [show k + 1 + 2 = k + 2 + 1 by omega, pow_succ]
    ring
  rw [hp] at h1
  change (countedWords (k + 3) : ℤ) - 2 * countedWords (k + 1) =
    2 * (2 : ℤ) ^ (k + 2) at h1
  simp only [a, if_neg (show k ≠ 0 by omega), if_neg (show k + 1 ≠ 0 by omega),
    if_neg (show k + 2 ≠ 0 by omega), if_neg (show k + 3 ≠ 0 by omega)]
  omega

open PowerSeries in
private theorem series :
    (1 - 2 * X) * (1 - 2 * X ^ 2) * PowerSeries.mk (fun n => (a n : ℤ)) =
      4 * X * (1 + X - 4 * X ^ 2) := by
  have hden : (1 - 2 * X : ℤ⟦X⟧) * (1 - 2 * X ^ 2) =
      1 - C 2 * X ^ 1 - C 2 * X ^ 2 + C 4 * X ^ 3 := by
    norm_num
    ring
  have hnum : (4 * X : ℤ⟦X⟧) * (1 + X - 4 * X ^ 2) =
      C 4 * X ^ 1 + C 4 * X ^ 2 - C 16 * X ^ 3 := by
    norm_num
    ring
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases hn : n < 4
  · have h0 : a 0 = 0 := by decide
    have h1 : a 1 = 4 := by decide
    have h2 : a 2 = 12 := by decide
    have h3 : a 3 = 16 := by decide
    interval_cases n <;> norm_num [h0, h1, h2, h3]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [if_pos (show 1 ≤ k + 3 by omega), if_pos (show 2 ≤ k + 3 by omega),
    if_pos (show 3 ≤ k + 3 by omega), if_neg (show k + 3 ≠ 1 by omega),
    if_neg (show k + 3 ≠ 2 by omega), if_neg (show k + 3 ≠ 3 by omega)]
  change (a (k + 3) : ℤ) - 2 * a (k + 2) - 2 * a (k + 1) + 4 * a k = _
  have h := recurrence k (by omega)
  omega

theorem solve : type_of% @main := ⟨series, even_count, odd_count⟩

end A253122

theorem OMA.solution : type_of% @OMA.S_oeis_a253122.main := A253122.solve
