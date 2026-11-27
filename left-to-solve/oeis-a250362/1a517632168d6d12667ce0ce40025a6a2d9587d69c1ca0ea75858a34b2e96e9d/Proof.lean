import OMAStatements.S_oeis_a250362
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace A250362

open OMA.S_oeis_a250362

private theorem common_lower {n : ℕ} (w : {w : ArrayChoice n // constantArray w}) :
    3 ≤ (w.val 0).val := by
  have h := w.property (3 : Fin 4)
  change (w.val 3).val + 3 = (w.val 0).val at h
  omega

private def badIndex {n : ℕ} (w : {w : ArrayChoice n // constantArray w}) : Fin (n - 2) :=
  ⟨(w.val 0).val - 3, by
    have hl := common_lower w
    have hu := (w.val 0).isLt
    omega⟩

private def badArray {n : ℕ} (c : Fin (n - 2)) : {w : ArrayChoice n // constantArray w} :=
  ⟨fun i => ⟨c.val + 3 - i.val, by have h := c.isLt; omega⟩, by
    intro i
    change c.val + 3 - i.val + i.val = c.val + 3 - 0
    have h := i.isLt
    omega⟩

private def badEquiv (n : ℕ) : {w : ArrayChoice n // constantArray w} ≃ Fin (n - 2) where
  toFun := badIndex
  invFun := badArray
  left_inv w := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    change (w.val 0).val - 3 + 3 - i.val = (w.val i).val
    have h := w.property i
    change (w.val i).val + i.val = (w.val 0).val at h
    have hl := common_lower w
    omega
  right_inv c := by
    apply Fin.ext
    change c.val + 3 - 0 - 3 = c.val
    omega

private theorem card_bad (n : ℕ) : Nat.card {w : ArrayChoice n // constantArray w} = n - 2 := by
  rw [Nat.card_congr (badEquiv n), Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem count (n : ℕ) (hn : 0 < n) : a n = (n + 1) ^ 4 - (n - 2) := by
  classical
  have h : Fintype.card {w : ArrayChoice n // constantArray w} = n - 2 := by
    rw [← Nat.card_eq_fintype_card, card_bad]
  unfold a
  rw [if_neg (by omega), Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_pi_const, Fintype.card_fin, h]

private theorem bad_le (n : ℕ) : n - 2 ≤ (n + 1) ^ 4 := by
  classical
  have h : Fintype.card {w : ArrayChoice n // constantArray w} = n - 2 := by
    rw [← Nat.card_eq_fintype_card, card_bad]
  have hp := Fintype.card_subtype_le (constantArray (n := n))
  rw [h, Fintype.card_pi_const, Fintype.card_fin] at hp
  exact hp

private theorem polynomial (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℤ) = ((n : ℤ) + 1)^4 - n + 2 := by
  rw [count n (by omega), Int.ofNat_sub (bad_le n), Int.ofNat_sub hn]
  push_cast
  ring

private theorem recurrence (n : ℕ) (hn : 2 ≤ n) :
    (a (n + 5) : ℤ) - 5 * a (n + 4) + 10 * a (n + 3) -
      10 * a (n + 2) + 5 * a (n + 1) - a n = 0 := by
  rw [polynomial (n + 5) (Nat.le_add_right_of_le hn),
    polynomial (n + 4) (Nat.le_add_right_of_le hn),
    polynomial (n + 3) (Nat.le_add_right_of_le hn),
    polynomial (n + 2) (Nat.le_add_right_of_le hn),
    polynomial (n + 1) (Nat.le_add_right_of_le hn), polynomial n hn]
  push_cast
  ring

open PowerSeries in
private theorem series :
    (1 - X) ^ 5 * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (16 + X + 10 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + X ^ 5) := by
  have hden : (1 - X : ℤ⟦X⟧) ^ 5 =
      1 - C 5 * X ^ 1 + C 10 * X ^ 2 - C 10 * X ^ 3 + C 5 * X ^ 4 - X ^ 5 := by
    norm_num
    ring
  have hnum : (X : ℤ⟦X⟧) * (16 + X + 10 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + X ^ 5) =
      C 16 * X ^ 1 + X ^ 2 + C 10 * X ^ 3 - C 2 * X ^ 4 - C 2 * X ^ 5 + X ^ 6 := by
    norm_num
    ring
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases hn : n < 7
  · have h0 : a 0 = 0 := by simp [a]
    have h1 := count 1 (by decide)
    have h2 := count 2 (by decide)
    have h3 := count 3 (by decide)
    have h4 := count 4 (by decide)
    have h5 := count 5 (by decide)
    have h6 := count 6 (by decide)
    norm_num at h1 h2 h3 h4 h5 h6
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5, h6]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [if_pos (show 1 ≤ k + 5 by omega), if_pos (show 2 ≤ k + 5 by omega),
    if_pos (show 3 ≤ k + 5 by omega), if_pos (show 4 ≤ k + 5 by omega),
    if_pos (show 5 ≤ k + 5 by omega), if_neg (show k + 5 ≠ 1 by omega),
    if_neg (show k + 5 ≠ 2 by omega), if_neg (show k + 5 ≠ 3 by omega),
    if_neg (show k + 5 ≠ 4 by omega), if_neg (show k + 5 ≠ 5 by omega),
    if_neg (show k + 5 ≠ 6 by omega)]
  change (a (k + 5) : ℤ) - 5 * a (k + 4) + 10 * a (k + 3) -
    10 * a (k + 2) + 5 * a (k + 1) - a k = _
  have hk := recurrence k (by omega)
  omega

private theorem exactRecurrence :
    ∀ n : ℕ, 6 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
        5 * a (n - 4) + a (n - 5) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hk := recurrence k (by omega)
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
    show k + 5 - 5 = k by omega]
  omega

theorem solve : type_of% @main := ⟨series, exactRecurrence⟩

end A250362

theorem OMA.solution : type_of% @OMA.S_oeis_a250362.main := A250362.solve
