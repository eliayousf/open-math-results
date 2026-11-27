import OMAStatements.S_oeis_a250364
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace A250364

open OMA.S_oeis_a250364
open scoped Classical

private abbrev Block (r : ℕ) := {s : Finset (Fin 6) // s.card = r}

private def uniform {n : ℕ} (w : ArrayChoice n) (s : Finset (Fin 6)) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, value w i = value w j

private theorem block_nonempty {r : ℕ} (h : 0 < r) (s : Block r) : s.val.Nonempty :=
  Finset.card_pos.mp (by rwa [s.property])

private def lower {r : ℕ} (h : 0 < r) (s : Block r) : Fin 6 :=
  s.val.min' (block_nonempty h s)

private def upper {r : ℕ} (h : 0 < r) (s : Block r) : Fin 6 :=
  s.val.max' (block_nonempty h s)

private theorem lower_mem {r : ℕ} (h : 0 < r) (s : Block r) : lower h s ∈ s.val :=
  Finset.min'_mem _ _

private theorem upper_mem {r : ℕ} (h : 0 < r) (s : Block r) : upper h s ∈ s.val :=
  Finset.max'_mem _ _

private theorem bounds {r : ℕ} (h : 0 < r) (s : Block r) {i : Fin 6} (hi : i ∈ s.val) :
    (lower h s).val ≤ i.val ∧ i.val ≤ (upper h s).val :=
  ⟨Finset.min'_le s.val i hi, Finset.le_max' s.val i hi⟩

private def gap {r : ℕ} (h : 0 < r) (s : Block r) : Fin 6 :=
  ⟨(upper h s).val - (lower h s).val,
    (Nat.sub_le _ _).trans_lt (upper h s).isLt⟩

private abbrev Outside {r : ℕ} (s : Block r) := {i : Fin 6 // i ∉ s.val}

private def encode {n r : ℕ} (h : 0 < r) (s : Block r)
    (w : {w : ArrayChoice n // uniform w s.val}) :
    Fin (n + 1 - (gap h s).val) × (Outside s → Fin (n + 1)) :=
  (⟨value w.val (lower h s) - (upper h s).val, by
    have e := w.property _ (lower_mem h s) _ (upper_mem h s)
    have hp := (w.val (lower h s)).isLt
    have hl := (bounds h s (upper_mem h s)).1
    unfold value at e
    change value w.val (lower h s) - (upper h s).val <
      n + 1 - ((upper h s).val - (lower h s).val)
    unfold value
    omega⟩, fun i => w.val i.val)

private def decode {n r : ℕ} (h : 0 < r) (s : Block r)
    (b : Fin (n + 1 - (gap h s).val) × (Outside s → Fin (n + 1))) :
    {w : ArrayChoice n // uniform w s.val} :=
  ⟨fun i => if hi : i ∈ s.val then
    ⟨b.1.val + (upper h s).val - i.val, by
      have hb := b.1.isLt
      have hl := (bounds h s hi).1
      have hlu := (bounds h s (upper_mem h s)).1
      change b.1.val < n + 1 - ((upper h s).val - (lower h s).val) at hb
      omega⟩ else b.2 ⟨i, hi⟩, by
    intro i hi j hj
    have hi' := (bounds h s hi).2
    have hj' := (bounds h s hj).2
    simp only [value, dif_pos hi, dif_pos hj]
    omega⟩

private def uniformEquiv {n r : ℕ} (h : 0 < r) (s : Block r) :
    {w : ArrayChoice n // uniform w s.val} ≃
      Fin (n + 1 - (gap h s).val) × (Outside s → Fin (n + 1)) where
  toFun := encode h s
  invFun := decode h s
  left_inv w := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s.val
    · apply Fin.ext
      have e0 := w.property _ (lower_mem h s) _ (upper_mem h s)
      have e1 := w.property _ (lower_mem h s) _ hi
      simp only [encode, decode, dif_pos hi, value] at *
      omega
    · simp [encode, decode, hi]
  right_inv b := by
    apply Prod.ext
    · apply Fin.ext
      have h₀ := (bounds h s (lower_mem h s)).2
      simp only [encode, decode, dif_pos (lower_mem h s), value]
      omega
    · funext i
      have hi := i.property
      simp [encode, decode, hi]

private theorem outside_card {r : ℕ} (s : Block r) :
    Fintype.card (Outside s) = 6 - r := by
  have hc : Fintype.card {i : Fin 6 // i ∈ s.val} = r := by
    rw [Fintype.card_subtype]
    simpa using s.property
  change Fintype.card {i : Fin 6 // ¬i ∈ s.val} = _
  rw [Fintype.card_subtype_compl, Fintype.card_fin, hc]

private theorem uniform_card (n : ℕ) {r : ℕ} (h : 0 < r) (s : Block r) :
    Fintype.card {w : ArrayChoice n // uniform w s.val} =
      (n + 1 - (gap h s).val) * (n + 1) ^ (6 - r) := by
  rw [Fintype.card_congr (uniformEquiv (n := n) h s),
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, outside_card]

private def gapCount {r : ℕ} (h : 0 < r) (d : Fin 6) : ℕ :=
  (Finset.univ.filter fun s : Block r => gap h s = d).card

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem gap_four : ∀ d : Fin 6, gapCount (r := 4) (by decide) d =
    if d.val = 3 then 3 else if d.val = 4 then 6 else if d.val = 5 then 6 else 0 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem gap_five : ∀ d : Fin 6, gapCount (r := 5) (by decide) d =
    if d.val = 4 then 2 else if d.val = 5 then 4 else 0 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem gap_six : ∀ d : Fin 6, gapCount (r := 6) (by decide) d =
    if d.val = 5 then 1 else 0 := by
  decide

private theorem sum_by_gap {r : ℕ} (h : 0 < r) (f : Fin 6 → ℕ) :
    (∑ s : Block r, f (gap h s)) = ∑ d : Fin 6, gapCount h d * f d := by
  calc
    _ = ∑ s : Block r, ∑ d : Fin 6, if gap h s = d then f d else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      simp
    _ = ∑ d : Fin 6, ∑ s : Block r, if gap h s = d then f d else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rfl

private noncomputable def totalBlocks (n r : ℕ) : ℕ :=
  ∑ s : Block r, Fintype.card {w : ArrayChoice n // uniform w s.val}

private theorem total_by_gap (n : ℕ) {r : ℕ} (h : 0 < r) :
    totalBlocks n r = ∑ d : Fin 6, gapCount h d * ((n + 1 - d.val) * (n + 1)^(6 - r)) := by
  unfold totalBlocks
  simp only [uniform_card n h]
  exact sum_by_gap h (fun d => (n + 1 - d.val) * (n + 1)^(6 - r))

private theorem total_four (n : ℕ) :
    totalBlocks n 4 = (n + 1)^2 * (3 * (n - 2) + 6 * (n - 3) + 6 * (n - 4)) := by
  rw [total_by_gap n (by decide : 0 < 4)]
  norm_num [gap_four, Fin.sum_univ_succ]
  rw [show n + 1 - 3 = n - 2 by omega, show n + 1 - 4 = n - 3 by omega,
    show n + 1 - 5 = n - 4 by omega]
  ring

private theorem total_five (n : ℕ) :
    totalBlocks n 5 = (n + 1) * (2 * (n - 3) + 4 * (n - 4)) := by
  rw [total_by_gap n (by decide : 0 < 5)]
  norm_num [gap_five, Fin.sum_univ_succ]
  rw [show n + 1 - 4 = n - 3 by omega, show n + 1 - 5 = n - 4 by omega]
  ring

private theorem total_six (n : ℕ) : totalBlocks n 6 = n - 4 := by
  rw [total_by_gap n (by decide : 0 < 6)]
  norm_num [gap_six, Fin.sum_univ_succ]
  omega

private theorem pos_mem {n : ℕ} {w : ArrayChoice n} {t : ℕ} {i : Fin 6} :
    i ∈ positions w t ↔ value w i = t := by simp [positions]

private theorem positions_small {n : ℕ} (w : ArrayChoice n) (t : ℕ) :
    (positions w t).card ≤ 6 := by
  simpa using Finset.card_le_univ (positions w t)

private theorem unique_value {n : ℕ} (w : ArrayChoice n) {x y : ℕ}
    (hx : 4 ≤ (positions w x).card) (hy : 4 ≤ (positions w y).card) : x = y := by
  by_contra h
  have hd : Disjoint (positions w x) (positions w y) := by
    exact Finset.disjoint_left.mpr fun i hix hiy => h ((pos_mem.mp hix).symm.trans (pos_mem.mp hiy))
  have hsum : (positions w x ∪ positions w y).card ≤ 6 := by
    simpa using Finset.card_le_univ (positions w x ∪ positions w y)
  rw [Finset.card_union_of_disjoint hd] at hsum
  omega

private theorem uniform_subset {n r : ℕ} (h : 0 < r) (w : ArrayChoice n) (s : Block r)
    (hs : uniform w s.val) : s.val ⊆ positions w (value w (lower h s)) := by
  intro i hi
  exact pos_mem.mpr (hs i hi _ (lower_mem h s))

private theorem uniform_large {n r : ℕ} (hr : 4 ≤ r) (w : ArrayChoice n) (s : Block r)
    (hs : uniform w s.val) : 4 ≤ (positions w (value w (lower (by omega) s))).card := by
  have hc := Finset.card_le_card (uniform_subset (by omega : 0 < r) w s hs)
  rw [s.property] at hc
  exact hr.trans hc

private abbrev Witness {n : ℕ} (w : ArrayChoice n) (r : ℕ) :=
  {s : Block r // uniform w s.val}

private def witnessEquiv {n r : ℕ} (hr : 4 ≤ r) (w : ArrayChoice n) (t : ℕ)
    (ht : 4 ≤ (positions w t).card) :
    Witness w r ≃ {s : Finset (Fin 6) // s ∈ (positions w t).powersetCard r} where
  toFun s :=
    ⟨s.val.val, Finset.mem_powersetCard.mpr ⟨by
      have hf := uniform_subset (by omega : 0 < r) w s.val s.property
      have hl := uniform_large hr w s.val s.property
      rwa [unique_value w hl ht] at hf, s.val.property⟩⟩
  invFun s :=
    ⟨⟨s.val, (Finset.mem_powersetCard.mp s.property).2⟩, by
      intro i hi j hj
      have hsub := (Finset.mem_powersetCard.mp s.property).1
      exact (pos_mem.mp (hsub hi)).trans (pos_mem.mp (hsub hj)).symm⟩
  left_inv s := Subtype.ext (Subtype.ext rfl)
  right_inv s := Subtype.ext rfl

private theorem witness_card {n r : ℕ} (hr : 4 ≤ r) (w : ArrayChoice n) (t : ℕ)
    (ht : 4 ≤ (positions w t).card) :
    Fintype.card (Witness w r) = (positions w t).card.choose r := by
  rw [Fintype.card_congr (witnessEquiv hr w t ht),
    Fintype.card_of_subtype _ (fun _ => Iff.rfl), Finset.card_powersetCard]

private theorem witness_empty {n r : ℕ} (hr : 4 ≤ r) (w : ArrayChoice n) (hb : ¬bad w) :
    Fintype.card (Witness w r) = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun s => hb ⟨_, uniform_large hr w s.val s.property⟩⟩

private theorem witness_total {n : ℕ} (w : ArrayChoice n) :
    Fintype.card (Witness w 4) + 10 * Fintype.card (Witness w 6) =
      4 * Fintype.card (Witness w 5) + (if bad w then 1 else 0) := by
  by_cases hb : bad w
  · obtain ⟨t, ht⟩ := hb
    have hb' : bad w := ⟨t, ht⟩
    rw [witness_card (by decide : 4 ≤ 4) w t ht, witness_card (by decide : 4 ≤ 6) w t ht,
      witness_card (by decide : 4 ≤ 5) w t ht, if_pos hb']
    have hu := positions_small w t
    generalize hm : (positions w t).card = m at *
    interval_cases m <;> decide
  · rw [witness_empty (by decide : 4 ≤ 4) w hb, witness_empty (by decide : 4 ≤ 6) w hb,
      witness_empty (by decide : 4 ≤ 5) w hb, if_neg hb]

private def swap (n r : ℕ) :
    (Σ s : Block r, {w : ArrayChoice n // uniform w s.val}) ≃
      (Σ w : ArrayChoice n, Witness w r) where
  toFun p := ⟨p.2.val, ⟨p.1, p.2.property⟩⟩
  invFun p := ⟨p.2.val, ⟨p.1, p.2.property⟩⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

private theorem total_as_witnesses (n r : ℕ) :
    totalBlocks n r = ∑ w : ArrayChoice n, Fintype.card (Witness w r) := by
  simpa only [totalBlocks, Fintype.card_sigma] using Fintype.card_congr (swap n r)

private theorem indicator {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] [Fintype {a // p a}] :
    (∑ x : α, if p x then 1 else 0) = Fintype.card {x // p x} := by
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

private theorem bad_equation (n : ℕ) :
    totalBlocks n 4 + 10 * totalBlocks n 6 =
      4 * totalBlocks n 5 + Fintype.card {w : ArrayChoice n // bad w} := by
  simp only [total_as_witnesses]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum, ← indicator bad,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => witness_total w

private theorem count_with_bad (n : ℕ) (hn : 0 < n) :
    a n + Fintype.card {w : ArrayChoice n // bad w} = (n + 1) ^ 6 := by
  have h := Fintype.card_subtype_le (bad (n := n))
  unfold a
  rw [if_neg (by omega), Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rw [Nat.sub_add_cancel h, Fintype.card_pi_const, Fintype.card_fin]

private theorem count_eq (n : ℕ) (hn : 0 < n) :
    a n + (n + 1)^2 * (3 * (n - 2) + 6 * (n - 3) + 6 * (n - 4)) + 10 * (n - 4) =
      (n + 1)^6 + 4 * ((n + 1) * (2 * (n - 3) + 4 * (n - 4))) := by
  have h0 := bad_equation n
  have h1 := count_with_bad n hn
  rw [total_four, total_five, total_six] at h0
  omega

private theorem count (n : ℕ) (hn : 0 < n) :
    a n = (n + 1)^6 + 4 * ((n + 1) * (2 * (n - 3) + 4 * (n - 4))) -
      ((n + 1)^2 * (3 * (n - 2) + 6 * (n - 3) + 6 * (n - 4)) + 10 * (n - 4)) := by
  have h := count_eq n hn
  omega

private theorem polynomial (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℤ) = (n : ℤ)^6 + 6 * n^5 + 15 * n^4 + 5 * n^3 + 57 * n^2 + 13 * n + 1 := by
  have h := congrArg (fun t : ℕ => (t : ℤ)) (count_eq n (by omega))
  push_cast at h
  rw [Int.ofNat_sub (show 2 ≤ n by omega), Int.ofNat_sub (show 3 ≤ n by omega),
    Int.ofNat_sub hn] at h
  norm_num at h
  calc
    (a n : ℤ) = (n + 1)^6 + 4 * ((n + 1) * (2 * (n - 3) + 4 * (n - 4))) -
      ((n + 1)^2 * (3 * (n - 2) + 6 * (n - 3) + 6 * (n - 4)) + 10 * (n - 4)) := by omega
    _ = _ := by ring

private theorem recurrence (n : ℕ) (hn : 4 ≤ n) :
    (a (n + 7) : ℤ) - 7 * a (n + 6) + 21 * a (n + 5) - 35 * a (n + 4) +
      35 * a (n + 3) - 21 * a (n + 2) + 7 * a (n + 1) - a n = 0 := by
  rw [polynomial (n + 7) (Nat.le_add_right_of_le hn), polynomial (n + 6) (Nat.le_add_right_of_le hn),
    polynomial (n + 5) (Nat.le_add_right_of_le hn), polynomial (n + 4) (Nat.le_add_right_of_le hn),
    polynomial (n + 3) (Nat.le_add_right_of_le hn), polynomial (n + 2) (Nat.le_add_right_of_le hn),
    polynomial (n + 1) (Nat.le_add_right_of_le hn), polynomial n hn]
  push_cast
  ring

open PowerSeries in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
private theorem series :
    (1 - X) ^ 7 * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (64 + 281 * X + 289 * X ^ 2 + 98 * X ^ 3 + 44 * X ^ 4 + 57 * X ^ 5 -
        405 * X ^ 6 + 482 * X ^ 7 - 232 * X ^ 8 + 42 * X ^ 9) := by
  have hden : (1 - X : ℤ⟦X⟧) ^ 7 =
      1 - C 7 * X ^ 1 + C 21 * X ^ 2 - C 35 * X ^ 3 +
        C 35 * X ^ 4 - C 21 * X ^ 5 + C 7 * X ^ 6 - X ^ 7 := by
    norm_num
    ring
  have hnum : (X : ℤ⟦X⟧) * (64 + 281 * X + 289 * X ^ 2 + 98 * X ^ 3 + 44 * X ^ 4 + 57 * X ^ 5 -
        405 * X ^ 6 + 482 * X ^ 7 - 232 * X ^ 8 + 42 * X ^ 9) =
      C 64 * X ^ 1 + C 281 * X ^ 2 + C 289 * X ^ 3 + C 98 * X ^ 4 +
        C 44 * X ^ 5 + C 57 * X ^ 6 - C 405 * X ^ 7 + C 482 * X ^ 8 - C 232 * X ^ 9 +
        C 42 * X ^ 10 := by
    norm_num
    ring
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases hn : n < 11
  · have h0 : a 0 = 0 := by simp [a]
    interval_cases n <;> norm_num [h0, count]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  simp only [if_pos (show 1 ≤ k + 7 by omega), if_pos (show 2 ≤ k + 7 by omega),
    if_pos (show 3 ≤ k + 7 by omega), if_pos (show 4 ≤ k + 7 by omega),
    if_pos (show 5 ≤ k + 7 by omega), if_pos (show 6 ≤ k + 7 by omega),
    if_pos (show 7 ≤ k + 7 by omega), if_neg (show k + 7 ≠ 1 by omega),
    if_neg (show k + 7 ≠ 2 by omega), if_neg (show k + 7 ≠ 3 by omega),
    if_neg (show k + 7 ≠ 4 by omega), if_neg (show k + 7 ≠ 5 by omega),
    if_neg (show k + 7 ≠ 6 by omega), if_neg (show k + 7 ≠ 7 by omega),
    if_neg (show k + 7 ≠ 8 by omega), if_neg (show k + 7 ≠ 9 by omega),
    if_neg (show k + 7 ≠ 10 by omega)]
  change (a (k + 7) : ℤ) - 7 * a (k + 6) + 21 * a (k + 5) - 35 * a (k + 4) +
    35 * a (k + 3) - 21 * a (k + 2) + 7 * a (k + 1) - a k = _
  have hk := recurrence k (by omega)
  omega

private theorem exactRecurrence :
    ∀ n : ℕ, 10 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) -
        35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  have hk := recurrence k (by omega)
  simp only [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
    show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega,
    show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega,
    show k + 7 - 7 = k by omega]
  omega

theorem solve : type_of% @main := ⟨series, exactRecurrence⟩

end A250364

theorem OMA.solution : type_of% @OMA.S_oeis_a250364.main := A250364.solve
