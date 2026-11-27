import OMAStatements.S_oeis_a243514
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace A243514

open OMA.S_oeis_a243514

private inductive WordClass where
  | constant
  | twoLetters
  | threeLetters
  | fourLetters
  | moreLetters
  deriving DecidableEq

private def classify (s : WordState) : WordClass :=
  match s.1.val with
  | 0 => .constant
  | 1 => .twoLetters
  | 2 => .threeLetters
  | 3 => .fourLetters
  | _ => .moreLetters

private def admissible (s : WordState) : Prop :=
  s.2.1 ≤ s.1 ∧ s.2.2 ≤ s.1 ∧ (s.1 = 0 ∨ s.2.1 ≠ s.2.2)

private instance (s : WordState) : Decidable (admissible s) :=
  by unfold admissible; infer_instance

private def transitions : WordClass → List WordClass
  | .constant => [.constant, .twoLetters]
  | .twoLetters => [.threeLetters]
  | .threeLetters => [.threeLetters, .fourLetters]
  | .fourLetters => [.fourLetters, .fourLetters, .moreLetters]
  | .moreLetters => [.moreLetters, .moreLetters, .moreLetters, .moreLetters]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem transfer :
    ∀ s : WordState, admissible s →
      (allowed s).map (fun z => classify (advance s z)) = transitions (classify s) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem advance_admissible :
    ∀ s : WordState, admissible s → ∀ z : Fin 6, z ∈ allowed s → admissible (advance s z) := by
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

private theorem count_more (k : ℕ) : count k .moreLetters = 4 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change count k .moreLetters + (count k .moreLetters + (count k .moreLetters +
      (count k .moreLetters + 0))) = 4 ^ (k + 1)
    rw [ih, pow_succ]
    omega

private theorem count_four (k : ℕ) : 2 * count k .fourLetters = 4 ^ k + 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 2 * (count k .fourLetters + (count k .fourLetters + (count k .moreLetters + 0))) =
      4 ^ (k + 1) + 2 ^ (k + 1)
    rw [count_more, pow_succ, pow_succ]
    omega

private theorem count_three (k : ℕ) :
    6 * count k .threeLetters = 2 + 3 * 2 ^ k + 4 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 6 * (count k .threeLetters + (count k .fourLetters + 0)) =
      2 + 3 * 2 ^ (k + 1) + 4 ^ (k + 1)
    have h := count_four k
    rw [pow_succ, pow_succ]
    omega

private theorem count_constant (n : ℕ) :
    18 * count (n + 1) .constant = 26 + 9 * 2 ^ n + 4 ^ n + 6 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change 18 * (count (k + 1) .constant + (count k .threeLetters + 0)) =
      26 + 9 * 2 ^ (k + 1) + 4 ^ (k + 1) + 6 * (k + 1)
    have h := count_three k
    rw [pow_succ, pow_succ]
    omega

private theorem closed (n : ℕ) (hn : 1 ≤ n) :
    18 * a n = 26 + 9 * 2 ^ n + 4 ^ n + 6 * n := by
  rw [a, if_neg (by omega), length_suffixes _ _ (by decide)]
  exact count_constant n

private theorem recur (n : ℕ) (hn : 1 ≤ n) :
    (a (n + 4) : ℤ) - 8 * a (n + 3) + 21 * a (n + 2) -
      22 * a (n + 1) + 8 * a n = 0 := by
  have h0 := closed n hn
  have h1 := closed (n + 1) (by omega)
  have h2 := closed (n + 2) (by omega)
  have h3 := closed (n + 3) (by omega)
  have h4 := closed (n + 4) (by omega)
  simp only [pow_succ (2 : ℕ), pow_succ (4 : ℕ)] at h1 h2 h3 h4
  omega

open PowerSeries in
private theorem series :
    (1 - X) ^ 2 * (1 - 2 * X) * (1 - 4 * X) *
      PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (3 - 19 * X + 33 * X ^ 2 - 16 * X ^ 3) := by
  have hden : (1 - X : ℤ⟦X⟧) ^ 2 * (1 - 2 * X) * (1 - 4 * X) =
      1 - C 8 * X ^ 1 + C 21 * X ^ 2 - C 22 * X ^ 3 + C 8 * X ^ 4 := by
    norm_num
    ring
  have hnum : (X : ℤ⟦X⟧) * (3 - 19 * X + 33 * X ^ 2 - 16 * X ^ 3) =
      C 3 * X ^ 1 - C 19 * X ^ 2 + C 33 * X ^ 3 - C 16 * X ^ 4 := by
    norm_num
    ring
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases hn : n < 5
  · have h0 : a 0 = 0 := by decide
    have h1 : a 1 = 3 := by decide
    have h2 : a 2 = 5 := by decide
    have h3 : a 3 = 10 := by decide
    have h4 : a 4 = 25 := by decide
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [if_pos (show 1 ≤ k + 4 by omega), if_pos (show 2 ≤ k + 4 by omega),
    if_pos (show 3 ≤ k + 4 by omega), if_pos (show 4 ≤ k + 4 by omega),
    if_neg (show k + 4 ≠ 1 by omega), if_neg (show k + 4 ≠ 2 by omega),
    if_neg (show k + 4 ≠ 3 by omega), if_neg (show k + 4 ≠ 4 by omega)]
  change (a (k + 4) : ℤ) - 8 * a (k + 3) + 21 * a (k + 2) -
    22 * a (k + 1) + 8 * a k = _
  have hk := recur k (by omega)
  omega

theorem solve : type_of% @main := ⟨series, closed⟩

end A243514

theorem OMA.solution : type_of% @OMA.S_oeis_a243514.main := A243514.solve
