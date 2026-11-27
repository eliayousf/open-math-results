import OMAStatements.S_oeis_a243516
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace A243516

open OMA.S_oeis_a243516

private inductive WordClass where
  | constant
  | twoLetters
  | threeLetters
  | fourLetters
  | fiveLetters
  | sixLetters
  | moreLetters
  deriving DecidableEq

private def classify (s : WordState) : WordClass :=
  match s.1.val with
  | 0 => .constant
  | 1 => .twoLetters
  | 2 => .threeLetters
  | 3 => .fourLetters
  | 4 => .fiveLetters
  | 5 => .sixLetters
  | _ => .moreLetters

private def admissible (s : WordState) : Prop :=
  s.2.1 ≤ s.1 ∧ s.2.2 ≤ s.1 ∧ (s.1 = 0 ∨ s.2.1 ≠ s.2.2)

private instance (s : WordState) : Decidable (admissible s) :=
  by unfold admissible; infer_instance

private def transitions : WordClass → List WordClass
  | .constant => [.constant, .twoLetters]
  | .twoLetters => [.threeLetters]
  | .threeLetters => [.threeLetters, .fourLetters]
  | .fourLetters => [.fourLetters, .fourLetters, .fiveLetters]
  | .fiveLetters => [.fiveLetters, .fiveLetters, .fiveLetters, .sixLetters]
  | .sixLetters => [.sixLetters, .sixLetters, .sixLetters, .sixLetters, .moreLetters]
  | .moreLetters =>
      [.moreLetters, .moreLetters, .moreLetters, .moreLetters, .moreLetters, .moreLetters]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem transfer :
    ∀ s : WordState, admissible s →
      (allowed s).map (fun z => classify (advance s z)) = transitions (classify s) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem advance_admissible :
    ∀ s : WordState, admissible s → ∀ z : Fin 8, z ∈ allowed s → admissible (advance s z) := by
  decide

private def count : ℕ → WordClass → ℕ
  | 0, _ => 1
  | k + 1, c => ((transitions c).map (count k)).sum

private theorem length_suffixes (k : ℕ) (s : WordState) (h : admissible s) :
    (suffixes s k).length = count k (classify s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [suffixes, List.length_flatMap, List.length_map, count]
    rw [← transfer s h, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun z hz =>
      ih _ (advance_admissible s h z hz))

private theorem count_more (k : ℕ) : count k .moreLetters = 6 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change count k .moreLetters + (count k .moreLetters + (count k .moreLetters +
      (count k .moreLetters + (count k .moreLetters + (count k .moreLetters + 0))))) =
      6 ^ (k + 1)
    rw [ih, pow_succ]
    omega

private theorem count_six (k : ℕ) : 2 * count k .sixLetters = 6 ^ k + 4 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 2 * (count k .sixLetters + (count k .sixLetters + (count k .sixLetters +
      (count k .sixLetters + (count k .moreLetters + 0))))) = 6 ^ (k + 1) + 4 ^ (k + 1)
    rw [count_more, pow_succ, pow_succ]
    omega

private theorem count_five (k : ℕ) :
    6 * count k .fiveLetters = 6 ^ k + 3 * 4 ^ k + 2 * 3 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 6 * (count k .fiveLetters + (count k .fiveLetters +
      (count k .fiveLetters + (count k .sixLetters + 0)))) =
      6 ^ (k + 1) + 3 * 4 ^ (k + 1) + 2 * 3 ^ (k + 1)
    have h := count_six k
    simp only [pow_succ (3 : ℕ), pow_succ (4 : ℕ), pow_succ (6 : ℕ)]
    omega

private theorem count_four (k : ℕ) :
    24 * count k .fourLetters = 6 ^ k + 6 * 4 ^ k + 8 * 3 ^ k + 9 * 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 24 * (count k .fourLetters + (count k .fourLetters + (count k .fiveLetters + 0))) =
      6 ^ (k + 1) + 6 * 4 ^ (k + 1) + 8 * 3 ^ (k + 1) + 9 * 2 ^ (k + 1)
    have h := count_five k
    simp only [pow_succ (2 : ℕ), pow_succ (3 : ℕ), pow_succ (4 : ℕ), pow_succ (6 : ℕ)]
    omega

private theorem count_three (k : ℕ) :
    120 * count k .threeLetters = 6 ^ k + 10 * 4 ^ k + 20 * 3 ^ k + 45 * 2 ^ k + 44 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 120 * (count k .threeLetters + (count k .fourLetters + 0)) =
      6 ^ (k + 1) + 10 * 4 ^ (k + 1) + 20 * 3 ^ (k + 1) + 45 * 2 ^ (k + 1) + 44
    have h := count_four k
    simp only [pow_succ (2 : ℕ), pow_succ (3 : ℕ), pow_succ (4 : ℕ), pow_succ (6 : ℕ)]
    omega

private theorem count_constant (n : ℕ) :
    1800 * count (n + 1) .constant =
      2722 + 675 * 2 ^ n + 50 * 4 ^ n + 150 * 3 ^ n + 3 * 6 ^ n + 660 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change 1800 * (count (k + 1) .constant + (count k .threeLetters + 0)) =
      2722 + 675 * 2 ^ (k + 1) + 50 * 4 ^ (k + 1) + 150 * 3 ^ (k + 1) +
        3 * 6 ^ (k + 1) + 660 * (k + 1)
    have h := count_three k
    simp only [pow_succ (2 : ℕ), pow_succ (3 : ℕ), pow_succ (4 : ℕ), pow_succ (6 : ℕ)]
    omega

private theorem closed_standard (n : ℕ) (hn : 1 ≤ n) :
    1800 * a n = 2722 + 675 * 2 ^ n + 50 * 4 ^ n + 150 * 3 ^ n + 3 * 6 ^ n + 660 * n := by
  rw [a, if_neg (by omega), length_suffixes _ _ (by decide)]
  exact count_constant n

private theorem closed (n : ℕ) (hn : 1 ≤ n) :
    1800 * a n = 2722 + 675 * 2 ^ n + 25 * 2 ^ (1 + 2 * n) +
      50 * 3 ^ (1 + n) + 2 ^ n * 3 ^ (1 + n) + 660 * n := by
  rw [closed_standard n hn]
  rw [show (6 : ℕ) ^ n = 2 ^ n * 3 ^ n from mul_pow 2 3 n]
  simp only [pow_add, pow_mul]
  ring

private theorem recurrence_from_closed (f : ℕ → ℕ)
    (form : ∀ i : ℕ, 1 ≤ i →
      1800 * f i = 2722 + 675 * 2 ^ i + 50 * 4 ^ i + 150 * 3 ^ i + 3 * 6 ^ i + 660 * i)
    (n : ℕ) (hn : 1 ≤ n) :
    (f (n + 6) : ℤ) - 17 * f (n + 5) + 111 * f (n + 4) -
      355 * f (n + 3) + 584 * f (n + 2) - 468 * f (n + 1) + 144 * f n = 0 := by
  have cast_form (i : ℕ) (hi : 1 ≤ i) :
      (1800 : ℤ) * f i = 2722 + 675 * 2 ^ i + 50 * 4 ^ i +
        150 * 3 ^ i + 3 * 6 ^ i + 660 * i := by
    exact_mod_cast form i hi
  have h1 := cast_form (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have h2 := cast_form (n + 2) (Nat.succ_le_succ (Nat.zero_le (n + 1)))
  have h3 := cast_form (n + 3) (Nat.succ_le_succ (Nat.zero_le (n + 2)))
  have h4 := cast_form (n + 4) (Nat.succ_le_succ (Nat.zero_le (n + 3)))
  have h5 := cast_form (n + 5) (Nat.succ_le_succ (Nat.zero_le (n + 4)))
  have h6 := cast_form (n + 6) (Nat.succ_le_succ (Nat.zero_le (n + 5)))
  have scaled :
      (1800 : ℤ) * (f (n + 6) - 17 * f (n + 5) + 111 * f (n + 4) -
        355 * f (n + 3) + 584 * f (n + 2) - 468 * f (n + 1) + 144 * f n) = 0 := by
    calc
      _ = 1800 * (f (n + 6) : ℤ) - 17 * (1800 * f (n + 5)) +
          111 * (1800 * f (n + 4)) - 355 * (1800 * f (n + 3)) +
          584 * (1800 * f (n + 2)) - 468 * (1800 * f (n + 1)) + 144 * (1800 * f n) := by ring
      _ = 0 := by
        rw [h6, h5, h4, h3, h2, h1, cast_form n hn]
        push_cast
        simp only [pow_add]
        ring
  exact (mul_eq_zero.mp scaled).resolve_left (by decide)

private theorem recur (n : ℕ) (hn : 1 ≤ n) :
    (a (n + 6) : ℤ) - 17 * a (n + 5) + 111 * a (n + 4) -
      355 * a (n + 3) + 584 * a (n + 2) - 468 * a (n + 1) + 144 * a n = 0 :=
  recurrence_from_closed a closed_standard n hn

open PowerSeries in
private theorem series :
    (1 - X) ^ 2 * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X) * (1 - 6 * X) *
      PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (3 - 46 * X + 258 * X ^ 2 - 655 * X ^ 3 + 739 * X ^ 4 - 288 * X ^ 5) := by
  have hden : (1 - X : ℤ⟦X⟧) ^ 2 * (1 - 2 * X) * (1 - 3 * X) *
      (1 - 4 * X) * (1 - 6 * X) =
      1 - C 17 * X ^ 1 + C 111 * X ^ 2 - C 355 * X ^ 3 +
        C 584 * X ^ 4 - C 468 * X ^ 5 + C 144 * X ^ 6 := by
    norm_num
    ring
  have hnum : (X : ℤ⟦X⟧) * (3 - 46 * X + 258 * X ^ 2 - 655 * X ^ 3 + 739 * X ^ 4 - 288 * X ^ 5) =
      C 3 * X ^ 1 - C 46 * X ^ 2 + C 258 * X ^ 3 - C 655 * X ^ 4 +
        C 739 * X ^ 5 - C 288 * X ^ 6 := by
    norm_num
    ring
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases hn : n < 7
  · have h0 : a 0 = 0 := by decide
    have h1 : a 1 = 3 := by decide
    have h2 : a 2 = 5 := by decide
    have h3 : a 3 = 10 := by decide
    have h4 : a 4 = 25 := by decide
    have h5 : a 5 = 77 := by decide
    have h6 : a 6 = 280 := by
      have h := closed_standard 6 (by decide)
      norm_num at h
      omega
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5, h6]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  simp only [if_pos (show 1 ≤ k + 6 by omega), if_pos (show 2 ≤ k + 6 by omega),
    if_pos (show 3 ≤ k + 6 by omega), if_pos (show 4 ≤ k + 6 by omega),
    if_pos (show 5 ≤ k + 6 by omega), if_pos (show 6 ≤ k + 6 by omega),
    if_neg (show k + 6 ≠ 1 by omega), if_neg (show k + 6 ≠ 2 by omega),
    if_neg (show k + 6 ≠ 3 by omega), if_neg (show k + 6 ≠ 4 by omega),
    if_neg (show k + 6 ≠ 5 by omega), if_neg (show k + 6 ≠ 6 by omega)]
  change (a (k + 6) : ℤ) - 17 * a (k + 5) + 111 * a (k + 4) -
    355 * a (k + 3) + 584 * a (k + 2) - 468 * a (k + 1) + 144 * a k = _
  have hk := recur k (by omega)
  omega

theorem solve : type_of% @main := ⟨series, closed⟩

end A243516

theorem OMA.solution : type_of% @OMA.S_oeis_a243516.main := A243516.solve
