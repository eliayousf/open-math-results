import OMAStatements.S_oeis_a243515
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace A243515

open OMA.S_oeis_a243515

private inductive WordClass where
  | constant
  | twoLetters
  | threeLetters
  | fourLetters
  | fiveLetters
  | moreLetters
  deriving DecidableEq

private def classify (s : WordState) : WordClass :=
  match s.1.val with
  | 0 => .constant
  | 1 => .twoLetters
  | 2 => .threeLetters
  | 3 => .fourLetters
  | 4 => .fiveLetters
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
  | .fiveLetters => [.fiveLetters, .fiveLetters, .fiveLetters, .moreLetters]
  | .moreLetters => [.moreLetters, .moreLetters, .moreLetters, .moreLetters, .moreLetters]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem transfer :
    ∀ s : WordState, admissible s →
      (allowed s).map (fun z => classify (advance s z)) = transitions (classify s) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem advance_admissible :
    ∀ s : WordState, admissible s → ∀ z : Fin 7, z ∈ allowed s → admissible (advance s z) := by
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

private theorem count_more (k : ℕ) : count k .moreLetters = 5 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change count k .moreLetters + (count k .moreLetters + (count k .moreLetters +
      (count k .moreLetters + (count k .moreLetters + 0)))) = 5 ^ (k + 1)
    rw [ih, pow_succ]
    omega

private theorem count_five (k : ℕ) : 2 * count k .fiveLetters = 5 ^ k + 3 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 2 * (count k .fiveLetters + (count k .fiveLetters +
      (count k .fiveLetters + (count k .moreLetters + 0)))) = 5 ^ (k + 1) + 3 ^ (k + 1)
    rw [count_more, pow_succ, pow_succ]
    omega

private theorem count_four (k : ℕ) :
    6 * count k .fourLetters = 5 ^ k + 3 * 3 ^ k + 2 * 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 6 * (count k .fourLetters + (count k .fourLetters + (count k .fiveLetters + 0))) =
      5 ^ (k + 1) + 3 * 3 ^ (k + 1) + 2 * 2 ^ (k + 1)
    have h := count_five k
    simp only [pow_succ (2 : ℕ), pow_succ (3 : ℕ), pow_succ (5 : ℕ)]
    omega

private theorem count_three (k : ℕ) :
    24 * count k .threeLetters = 5 ^ k + 6 * 3 ^ k + 8 * 2 ^ k + 9 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 24 * (count k .threeLetters + (count k .fourLetters + 0)) =
      5 ^ (k + 1) + 6 * 3 ^ (k + 1) + 8 * 2 ^ (k + 1) + 9
    have h := count_four k
    simp only [pow_succ (2 : ℕ), pow_succ (3 : ℕ), pow_succ (5 : ℕ)]
    omega

private theorem count_constant (n : ℕ) :
    96 * count (n + 1) .constant = 147 + 32 * 2 ^ n + 12 * 3 ^ n + 5 ^ n + 36 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change 96 * (count (k + 1) .constant + (count k .threeLetters + 0)) =
      147 + 32 * 2 ^ (k + 1) + 12 * 3 ^ (k + 1) + 5 ^ (k + 1) + 36 * (k + 1)
    have h := count_three k
    simp only [pow_succ (2 : ℕ), pow_succ (3 : ℕ), pow_succ (5 : ℕ)]
    omega

private theorem closed_standard (n : ℕ) (hn : 1 ≤ n) :
    96 * a n = 147 + 32 * 2 ^ n + 12 * 3 ^ n + 5 ^ n + 36 * n := by
  rw [a, if_neg (by omega), length_suffixes _ _ (by decide)]
  exact count_constant n

private theorem closed (n : ℕ) (hn : 1 ≤ n) :
    96 * a n = 147 + 2 ^ (5 + n) + 4 * 3 ^ (1 + n) + 5 ^ n + 36 * n := by
  rw [closed_standard n hn]
  simp only [pow_add]
  ring

private theorem recur (n : ℕ) (hn : 1 ≤ n) :
    (a (n + 5) : ℤ) - 12 * a (n + 4) + 52 * a (n + 3) -
      102 * a (n + 2) + 91 * a (n + 1) - 30 * a n = 0 := by
  have h0 := closed_standard n hn
  have h1 := closed_standard (n + 1) (by omega)
  have h2 := closed_standard (n + 2) (by omega)
  have h3 := closed_standard (n + 3) (by omega)
  have h4 := closed_standard (n + 4) (by omega)
  have h5 := closed_standard (n + 5) (by omega)
  simp only [pow_succ (2 : ℕ), pow_succ (3 : ℕ), pow_succ (5 : ℕ)] at h1 h2 h3 h4 h5
  omega

open PowerSeries in
private theorem series :
    (1 - X) ^ 2 * (1 - 2 * X) * (1 - 3 * X) * (1 - 5 * X) *
      PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (3 - 31 * X + 106 * X ^ 2 - 141 * X ^ 3 + 60 * X ^ 4) := by
  have hden : (1 - X : ℤ⟦X⟧) ^ 2 * (1 - 2 * X) * (1 - 3 * X) * (1 - 5 * X) =
      1 - C 12 * X ^ 1 + C 52 * X ^ 2 - C 102 * X ^ 3 +
        C 91 * X ^ 4 - C 30 * X ^ 5 := by
    norm_num
    ring
  have hnum : (X : ℤ⟦X⟧) * (3 - 31 * X + 106 * X ^ 2 - 141 * X ^ 3 + 60 * X ^ 4) =
      C 3 * X ^ 1 - C 31 * X ^ 2 + C 106 * X ^ 3 - C 141 * X ^ 4 + C 60 * X ^ 5 := by
    norm_num
    ring
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases hn : n < 6
  · have h0 : a 0 = 0 := by decide
    have h1 : a 1 = 3 := by decide
    have h2 : a 2 = 5 := by decide
    have h3 : a 3 = 10 := by decide
    have h4 : a 4 = 25 := by decide
    have h5 : a 5 = 77 := by decide
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [if_pos (show 1 ≤ k + 5 by omega), if_pos (show 2 ≤ k + 5 by omega),
    if_pos (show 3 ≤ k + 5 by omega), if_pos (show 4 ≤ k + 5 by omega),
    if_pos (show 5 ≤ k + 5 by omega), if_neg (show k + 5 ≠ 1 by omega),
    if_neg (show k + 5 ≠ 2 by omega), if_neg (show k + 5 ≠ 3 by omega),
    if_neg (show k + 5 ≠ 4 by omega), if_neg (show k + 5 ≠ 5 by omega)]
  change (a (k + 5) : ℤ) - 12 * a (k + 4) + 52 * a (k + 3) -
    102 * a (k + 2) + 91 * a (k + 1) - 30 * a k = _
  have hk := recur k (by omega)
  omega

theorem solve : type_of% @main := ⟨series, closed⟩

end A243515

theorem OMA.solution : type_of% @OMA.S_oeis_a243515.main := A243515.solve
