import OMAStatements.S_oeis_a243513

namespace A243513

open OMA.S_oeis_a243513

private inductive WordClass where
  | constant
  | twoLetters
  | threeLetters
  | moreLetters
  deriving DecidableEq

private def classify (s : WordState) : WordClass :=
  match s.1.val with
  | 0 => .constant
  | 1 => .twoLetters
  | 2 => .threeLetters
  | _ => .moreLetters

private def admissible (s : WordState) : Prop :=
  s.2.1 ≤ s.1 ∧ s.2.2 ≤ s.1 ∧ (s.1 = 0 ∨ s.2.1 ≠ s.2.2)

private instance (s : WordState) : Decidable (admissible s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (_ ∨ _)))

private def transitions : WordClass → List WordClass
  | .constant => [.constant, .twoLetters]
  | .twoLetters => [.threeLetters]
  | .threeLetters => [.threeLetters, .moreLetters]
  | .moreLetters => [.moreLetters, .moreLetters, .moreLetters]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem transfer :
    ∀ s : WordState, admissible s →
      (allowed s).map (fun z => classify (advance s z)) = transitions (classify s) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem advance_admissible :
    ∀ s : WordState, admissible s → ∀ z : Fin 5, z ∈ allowed s → admissible (advance s z) := by
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

private theorem count_more (k : ℕ) : count k .moreLetters = 3 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change count k .moreLetters + (count k .moreLetters + (count k .moreLetters + 0)) =
      3 ^ (k + 1)
    rw [ih, pow_succ]
    omega

private theorem count_three (k : ℕ) : 2 * count k .threeLetters = 3 ^ k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 2 * (count k .threeLetters + (count k .moreLetters + 0)) =
      3 ^ (k + 1) + 1
    rw [count_more, pow_succ]
    omega

private theorem count_constant (n : ℕ) :
    4 * count (n + 1) .constant = 7 + 3 ^ n + 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change 4 * (count (k + 1) .constant + (count k .threeLetters + 0)) =
      7 + 3 ^ (k + 1) + 2 * (k + 1)
    have h := count_three k
    rw [pow_succ]
    omega

private theorem closed (n : ℕ) (hn : 1 ≤ n) : 4 * a n = 7 + 3 ^ n + 2 * n := by
  rw [a, if_neg (by omega), length_suffixes _ _ (by decide)]
  exact count_constant n

private theorem recur (n : ℕ) (hn : 1 ≤ n) :
    (a (n + 3) : ℤ) - 5 * a (n + 2) + 7 * a (n + 1) - 3 * a n = 0 := by
  have h0 := closed n hn
  have h1 := closed (n + 1) (by omega)
  have h2 := closed (n + 2) (by omega)
  have h3 := closed (n + 3) (by omega)
  rw [pow_succ] at h1
  rw [pow_succ, pow_succ] at h2
  rw [pow_succ, pow_succ, pow_succ] at h3
  omega

open PowerSeries in
private theorem series :
    (1 - X) ^ 2 * (1 - 3 * X) * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (3 - 10 * X + 6 * X ^ 2) := by
  have hden : (1 - X : ℤ⟦X⟧) ^ 2 * (1 - 3 * X) =
      1 - C 5 * X ^ 1 + C 7 * X ^ 2 - C 3 * X ^ 3 := by
    norm_num
    ring
  have hnum : (X : ℤ⟦X⟧) * (3 - 10 * X + 6 * X ^ 2) =
      C 3 * X ^ 1 - C 10 * X ^ 2 + C 6 * X ^ 3 := by
    norm_num
    ring
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases hn : n < 4
  · have h0 : a 0 = 0 := by decide
    have h1 : a 1 = 3 := by decide
    have h2 : a 2 = 5 := by decide
    have h3 : a 3 = 10 := by decide
    interval_cases n <;> norm_num [h0, h1, h2, h3]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [if_pos (show 1 ≤ k + 3 by omega), if_pos (show 2 ≤ k + 3 by omega),
    if_pos (show 3 ≤ k + 3 by omega), if_neg (show k + 3 ≠ 1 by omega),
    if_neg (show k + 3 ≠ 2 by omega), if_neg (show k + 3 ≠ 3 by omega)]
  change (a (k + 3) : ℤ) - 5 * a (k + 2) + 7 * a (k + 1) - 3 * a k = _
  have hk := recur k (by omega)
  omega

theorem solve : type_of% @main := ⟨series, closed⟩

end A243513

theorem OMA.solution : type_of% @OMA.S_oeis_a243513.main := A243513.solve
