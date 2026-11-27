import OMAStatements.S_oeis_a250363
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace A250363

open OMA.S_oeis_a250363
open scoped Classical

private def lower (i : Fin 5) : Fin 5 := if i = 0 then 1 else 0

private def upper (i : Fin 5) : Fin 5 := if i = 4 then 3 else 4

private theorem lower_ne : ∀ i : Fin 5, lower i ≠ i := by decide

private theorem upper_ne : ∀ i : Fin 5, upper i ≠ i := by decide

private theorem bounds :
    ∀ i j : Fin 5, j ≠ i → (lower i).val ≤ j.val ∧ j.val ≤ (upper i).val := by
  decide

private def room (n : ℕ) (i : Fin 5) : ℕ :=
  n + (lower i).val + 1 - (upper i).val

private def encode {n : ℕ} (i : Fin 5) (w : {w : ArrayChoice n // equalOutside w i}) :
    Fin (n + 1) × Fin (room n i) :=
  (w.val i, ⟨value w.val (lower i) - (upper i).val, by
    have h := w.property (lower i) (upper i) (lower_ne i) (upper_ne i)
    have h0 := (w.val (lower i)).isLt
    unfold room value at *
    omega⟩)

private def decode {n : ℕ} (i : Fin 5) (b : Fin (n + 1) × Fin (room n i)) :
    {w : ArrayChoice n // equalOutside w i} :=
  ⟨fun j => if h : j = i then b.1 else
    ⟨b.2.val + (upper i).val - j.val, by
      have hb := b.2.isLt
      have h0 := (bounds i j h).1
      unfold room at hb
      omega⟩, by
    intro j k hj hk
    have hj' := (bounds i j hj).2
    have hk' := (bounds i k hk).2
    simp only [value, dif_neg hj, dif_neg hk]
    omega⟩

private def omissionEquiv (n : ℕ) (i : Fin 5) :
    {w : ArrayChoice n // equalOutside w i} ≃ Fin (n + 1) × Fin (room n i) where
  toFun := encode i
  invFun := decode i
  left_inv w := by
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · subst j
      simp [encode, decode]
    · apply Fin.ext
      have h0 := w.property (lower i) (upper i) (lower_ne i) (upper_ne i)
      have h1 := w.property (lower i) j (lower_ne i) hj
      simp only [encode, decode, dif_neg hj, value] at *
      omega
  right_inv b := by
    apply Prod.ext
    · simp [encode, decode]
    · apply Fin.ext
      have hb := (bounds i (lower i) (lower_ne i)).2
      simp only [encode, decode, dif_neg (lower_ne i), value]
      omega

private theorem omitted_card (n : ℕ) (i : Fin 5) :
    Fintype.card {w : ArrayChoice n // equalOutside w i} = (n + 1) * room n i := by
  classical
  rw [Fintype.card_congr (omissionEquiv n i), Fintype.card_prod]
  simp

private theorem sum_omitted (n : ℕ) :
    (∑ i : Fin 5, Fintype.card {w : ArrayChoice n // equalOutside w i}) =
      (n + 1) * (2 * (n - 2) + 3 * (n - 3)) := by
  classical
  simp only [omitted_card, ← Finset.mul_sum]
  congr 1
  simp [Fin.sum_univ_succ, room, lower, upper]
  omega

private def constant {n : ℕ} (w : ArrayChoice n) : Prop :=
  ∀ i : Fin 5, value w i = value w 0

private theorem constant_lower {n : ℕ} (w : {w : ArrayChoice n // constant w}) :
    4 ≤ (w.val 0).val := by
  have h := w.property (4 : Fin 5)
  change (w.val 4).val + 4 = (w.val 0).val at h
  omega

private def constantIndex {n : ℕ} (w : {w : ArrayChoice n // constant w}) : Fin (n - 3) :=
  ⟨(w.val 0).val - 4, by
    have hl := constant_lower w
    have hu := (w.val 0).isLt
    omega⟩

private def constantArray {n : ℕ} (c : Fin (n - 3)) : {w : ArrayChoice n // constant w} :=
  ⟨fun i => ⟨c.val + 4 - i.val, by have h := c.isLt; omega⟩, by
    intro i
    change c.val + 4 - i.val + i.val = c.val + 4 - 0
    have h := i.isLt
    omega⟩

private def constantEquiv (n : ℕ) : {w : ArrayChoice n // constant w} ≃ Fin (n - 3) where
  toFun := constantIndex
  invFun := constantArray
  left_inv w := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    change (w.val 0).val - 4 + 4 - i.val = (w.val i).val
    have h := w.property i
    change (w.val i).val + i.val = (w.val 0).val at h
    have hl := constant_lower w
    omega
  right_inv c := by
    apply Fin.ext
    change c.val + 4 - 0 - 4 = c.val
    omega

private theorem constant_card (n : ℕ) :
    Fintype.card {w : ArrayChoice n // constant w} = n - 3 := by
  classical
  rw [Fintype.card_congr (constantEquiv n), Fintype.card_fin]

private theorem other : ∀ i j : Fin 5, ∃ k : Fin 5, k ≠ i ∧ k ≠ j := by decide

private theorem constant_of_two {n : ℕ} {w : ArrayChoice n} {i j : Fin 5}
    (hij : i ≠ j) (hi : equalOutside w i) (hj : equalOutside w j) : constant w := by
  obtain ⟨k, hki, hkj⟩ := other i j
  have hk (r : Fin 5) : value w r = value w k := by
    by_cases hr : r = i
    · subst r
      exact hj i k hij hkj
    · exact hi r k hr hki
  intro r
  exact (hk r).trans (hk 0).symm

private theorem witnesses {n : ℕ} (w : ArrayChoice n) [Decidable (bad w)]
    [Decidable (constant w)] [Fintype {i : Fin 5 // equalOutside w i}] :
    Fintype.card {i : Fin 5 // equalOutside w i} =
      (if bad w then 1 else 0) + (if constant w then 4 else 0) := by
  classical
  by_cases hc : constant w
  · have hw (i : Fin 5) : equalOutside w i := by
      intro j k _ _
      exact (hc j).trans (hc k).symm
    have hb : bad w := ⟨0, hw 0⟩
    let e : {i : Fin 5 // equalOutside w i} ≃ Fin 5 :=
      { toFun := Subtype.val
        invFun := fun i => ⟨i, hw i⟩
        left_inv := fun i => Subtype.ext rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_fin, if_pos hb, if_pos hc]
  · by_cases hb : bad w
    · obtain ⟨i, hi⟩ := hb
      have hb' : bad w := ⟨i, hi⟩
      let e : {j : Fin 5 // equalOutside w j} ≃ PUnit.{1} :=
        { toFun := fun _ => PUnit.unit
          invFun := fun _ => ⟨i, hi⟩
          left_inv := fun j => Subtype.ext (by
            by_contra hn
            exact hc (constant_of_two hn hi j.property))
          right_inv := fun j => by cases j; rfl }
      rw [Fintype.card_congr e, Fintype.card_punit, if_pos hb', if_neg hc]
    · have he : IsEmpty {i : Fin 5 // equalOutside w i} := ⟨fun i => hb ⟨i.val, i.property⟩⟩
      rw [Fintype.card_eq_zero_iff.mpr he, if_neg hb, if_neg hc]

private def swap (n : ℕ) :
    (Σ i : Fin 5, {w : ArrayChoice n // equalOutside w i}) ≃
      (Σ w : ArrayChoice n, {i : Fin 5 // equalOutside w i}) where
  toFun s := ⟨s.2.val, ⟨s.1, s.2.property⟩⟩
  invFun s := ⟨s.2.val, ⟨s.1, s.2.property⟩⟩
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

private theorem indicator {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] [Fintype {a // p a}] :
    (∑ x : α, if p x then 1 else 0) = Fintype.card {x // p x} := by
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

private theorem bad_equation (n : ℕ) :
    Fintype.card {w : ArrayChoice n // bad w} + 4 * (n - 3) =
      (n + 1) * (2 * (n - 2) + 3 * (n - 3)) := by
  classical
  have hswap : (∑ i : Fin 5, Fintype.card {w : ArrayChoice n // equalOutside w i}) =
      (∑ w : ArrayChoice n, Fintype.card {i : Fin 5 // equalOutside w i}) := by
    simpa only [Fintype.card_sigma] using Fintype.card_congr (swap n)
  have h4 : (∑ w : ArrayChoice n, if constant w then 4 else 0) =
      4 * Fintype.card {w : ArrayChoice n // constant w} := by
    rw [← indicator constant, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : constant w <;> simp [h]
  rw [sum_omitted n] at hswap
  simp only [witnesses, Finset.sum_add_distrib, indicator, h4, constant_card] at hswap
  exact hswap.symm

private theorem count_with_bad (n : ℕ) (hn : 0 < n) :
    a n + Fintype.card {w : ArrayChoice n // bad w} = (n + 1) ^ 5 := by
  classical
  have h := Fintype.card_subtype_le (bad (n := n))
  unfold a
  rw [if_neg (by omega), Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rw [Nat.sub_add_cancel h, Fintype.card_pi_const, Fintype.card_fin]

private theorem count_eq (n : ℕ) (hn : 0 < n) :
    a n + (n + 1) * (2 * (n - 2) + 3 * (n - 3)) = (n + 1)^5 + 4 * (n - 3) := by
  have h0 := bad_equation n
  have h1 := count_with_bad n hn
  omega

private theorem polynomial (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℤ) = ((n : ℤ) + 1)^5 - 5 * n^2 + 12 * n + 1 := by
  have h := congrArg (fun t : ℕ => (t : ℤ)) (count_eq n (by omega))
  push_cast at h
  rw [Int.ofNat_sub (show 2 ≤ n by omega), Int.ofNat_sub hn] at h
  norm_num at h
  calc
    (a n : ℤ) = (n + 1)^5 + 4 * (n - 3) -
        ((n : ℤ) + 1) * (2 * (n - 2) + 3 * (n - 3)) := by omega
    _ = ((n : ℤ) + 1)^5 - 5 * n^2 + 12 * n + 1 := by ring

private theorem recurrence (n : ℕ) (hn : 3 ≤ n) :
    (a (n + 6) : ℤ) - 6 * a (n + 5) + 15 * a (n + 4) - 20 * a (n + 3) +
      15 * a (n + 2) - 6 * a (n + 1) + a n = 0 := by
  rw [polynomial (n + 6) (Nat.le_add_right_of_le hn),
    polynomial (n + 5) (Nat.le_add_right_of_le hn),
    polynomial (n + 4) (Nat.le_add_right_of_le hn),
    polynomial (n + 3) (Nat.le_add_right_of_le hn),
    polynomial (n + 2) (Nat.le_add_right_of_le hn),
    polynomial (n + 1) (Nat.le_add_right_of_le hn), polynomial n hn]
  push_cast
  ring

open PowerSeries in
set_option maxRecDepth 6000 in
private theorem series :
    (1 - X) ^ 6 * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (32 + 51 * X + 38 * X ^ 2 + 3 * X ^ 3 + 8 * X ^ 4 -
        29 * X ^ 5 + 22 * X ^ 6 - 5 * X ^ 7) := by
  have hden : (1 - X : ℤ⟦X⟧) ^ 6 =
      1 - C 6 * X ^ 1 + C 15 * X ^ 2 - C 20 * X ^ 3 +
        C 15 * X ^ 4 - C 6 * X ^ 5 + X ^ 6 := by
    norm_num
    ring
  have hnum : (X : ℤ⟦X⟧) * (32 + 51 * X + 38 * X ^ 2 + 3 * X ^ 3 + 8 * X ^ 4 -
        29 * X ^ 5 + 22 * X ^ 6 - 5 * X ^ 7) =
      C 32 * X ^ 1 + C 51 * X ^ 2 + C 38 * X ^ 3 + C 3 * X ^ 4 +
        C 8 * X ^ 5 - C 29 * X ^ 6 + C 22 * X ^ 7 - C 5 * X ^ 8 := by
    norm_num
    ring
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases hn : n < 9
  · have h0 : a 0 = 0 := by simp [a]
    have h1 : a 1 = 32 := by have h := count_eq 1 (by decide); norm_num at h; omega
    have h2 : a 2 = 243 := by have h := count_eq 2 (by decide); norm_num at h; omega
    have h3 : a 3 = 1016 := by have h := count_eq 3 (by decide); norm_num at h; omega
    have h4 : a 4 = 3094 := by have h := count_eq 4 (by decide); norm_num at h; omega
    have h5 : a 5 = 7712 := by have h := count_eq 5 (by decide); norm_num at h; omega
    have h6 : a 6 = 16700 := by have h := count_eq 6 (by decide); norm_num at h; omega
    have h7 : a 7 = 32608 := by have h := count_eq 7 (by decide); norm_num at h; omega
    have h8 : a 8 = 58826 := by have h := count_eq 8 (by decide); norm_num at h; omega
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  simp only [if_pos (show 1 ≤ k + 6 by omega), if_pos (show 2 ≤ k + 6 by omega),
    if_pos (show 3 ≤ k + 6 by omega), if_pos (show 4 ≤ k + 6 by omega),
    if_pos (show 5 ≤ k + 6 by omega), if_pos (show 6 ≤ k + 6 by omega),
    if_neg (show k + 6 ≠ 1 by omega), if_neg (show k + 6 ≠ 2 by omega),
    if_neg (show k + 6 ≠ 3 by omega), if_neg (show k + 6 ≠ 4 by omega),
    if_neg (show k + 6 ≠ 5 by omega), if_neg (show k + 6 ≠ 6 by omega),
    if_neg (show k + 6 ≠ 7 by omega), if_neg (show k + 6 ≠ 8 by omega)]
  change (a (k + 6) : ℤ) - 6 * a (k + 5) + 15 * a (k + 4) - 20 * a (k + 3) +
    15 * a (k + 2) - 6 * a (k + 1) + a k = _
  have hk := recurrence k (by omega)
  omega

private theorem exactRecurrence :
    ∀ n : ℕ, 8 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
        15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have hk := recurrence k (by omega)
  simp only [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
    show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
    show k + 6 - 5 = k + 1 by omega, show k + 6 - 6 = k by omega]
  omega

theorem solve : type_of% @main := ⟨series, exactRecurrence⟩

end A250363

theorem OMA.solution : type_of% @OMA.S_oeis_a250363.main := A250363.solve
