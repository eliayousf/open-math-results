import OMAStatements.S_oeis_a081732
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Digits.Lemmas

namespace OpenMath.A081732

open Finset
open OMA.S_oeis_a081732 (Digit Word pref firstDigit deletions insertions substitutions canonical count trit numeral a)

private theorem canonical_pref (d : Digit) (s : Word) (h : 2 ≤ s.length) :
    canonical (d :: s) ↔ canonical s := by
  cases s with
  | nil => simp at h
  | cons x xs =>
    cases xs with
    | nil => simp at h
    | cons y ys =>
      simp [canonical, List.getLast?_cons]

private theorem delete_length {s t : Word} (ht : t ∈ deletions s) :
    t.length + 1 = s.length := by
  induction s generalizing t with
  | nil => simp [deletions] at ht
  | cons d s ih =>
    rw [deletions, mem_insert] at ht
    rcases ht with rfl | ht
    · rfl
    · obtain ⟨v,hv,rfl⟩ := mem_map.mp ht
      have h := ih hv
      change (d :: v).length + 1 = (d :: s).length
      simp only [List.length_cons]
      omega

private theorem insert_length {s t : Word} (ht : t ∈ insertions s) :
    t.length = s.length + 1 := by
  induction s generalizing t with
  | nil =>
    obtain ⟨v,_,rfl⟩ := mem_map.mp ht
    rfl
  | cons d s ih =>
    rw [insertions, mem_union] at ht
    rcases ht with ht | ht
    · obtain ⟨v,_,rfl⟩ := mem_map.mp ht
      rfl
    · obtain ⟨v,hv,rfl⟩ := mem_map.mp ht
      have h := ih hv
      change (d :: v).length = (d :: s).length + 1
      simp only [List.length_cons]
      omega

private theorem sub_length {s t : Word} (ht : t ∈ substitutions s) :
    t.length = s.length := by
  induction s generalizing t with
  | nil => simp [substitutions] at ht
  | cons d s ih =>
    rw [substitutions, mem_union] at ht
    rcases ht with ht | ht
    · obtain ⟨v,_,rfl⟩ := mem_map.mp ht
      rfl
    · obtain ⟨v,hv,rfl⟩ := mem_map.mp ht
      have h := ih hv
      change (d :: v).length = (d :: s).length
      simp only [List.length_cons]
      omega

private theorem valid_map (d : Digit) (S : Finset Word) (hlen : ∀ w ∈ S, 2 ≤ w.length) :
    (S.map (pref d)).filter canonical = (S.filter canonical).map (pref d) := by
  ext u
  simp only [mem_filter, mem_map]
  constructor
  · rintro ⟨⟨v,hv,rfl⟩,hg⟩
    exact ⟨v, ⟨hv,(canonical_pref d v (hlen v hv)).mp hg⟩, rfl⟩
  · rintro ⟨v,⟨hv,hg⟩,rfl⟩
    exact ⟨⟨v,hv,rfl⟩,(canonical_pref d v (hlen v hv)).mpr hg⟩


private theorem delete_step (d : Digit) (s : Word) (hs : canonical s)
    (hlen : 3 ≤ s.length) :
    ((deletions (d :: s)).filter canonical).card =
      ((deletions s).filter canonical).card + if s.head? = some d then 0 else 1 := by
  have hmem : s ∈ ((deletions s).filter canonical).map (pref d) ↔
      s.head? = some d := by
    constructor
    · intro h
      obtain ⟨v,_,hv⟩ := mem_map.mp h
      rw [← hv]
      rfl
    · intro h
      cases s with
      | nil => simp at hlen
      | cons c cs =>
        have hc : c = d := by simpa using h
        subst c
        apply mem_map.mpr
        refine ⟨cs, mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
        · simp [deletions]
        · have hcLen : 2 ≤ cs.length := by
            simp only [List.length_cons] at hlen
            omega
          exact (canonical_pref d cs hcLen).mp hs
  rw [deletions, filter_insert, if_pos hs,
    valid_map d (deletions s) (by intro t ht; have h := delete_length ht; omega)]
  by_cases h : s.head? = some d
  · rw [if_pos h, add_zero, insert_eq_of_mem (hmem.mpr h), card_map]
  · rw [if_neg h, card_insert_of_notMem (mt hmem.mp h), card_map]

private theorem add_front (d : Digit) (s : Word) (S : Finset Word)
    (hs : canonical s) (hlen : 2 ≤ s.length) (hS : ∀ v ∈ S, 2 ≤ v.length) :
    ((((univ.erase d).map (firstDigit s)) ∪ S.map (pref d)).filter canonical).card =
      2 + (S.filter canonical).card := by
  let f := (univ.erase d).map (firstDigit s)
  change ((f ∪ S.map (pref d)).filter canonical).card = _
  have hf : f.filter canonical = f := by
    apply filter_eq_self.mpr
    intro v hv
    have hv' : v ∈ (univ.erase d).map (firstDigit s) := hv
    obtain ⟨c,_,rfl⟩ := mem_map.mp hv'
    exact (canonical_pref c s hlen).mpr hs
  have hd : Disjoint f ((S.filter canonical).map (pref d)) := by
    rw [disjoint_left]
    intro x hx hxd
    have hx' : x ∈ (univ.erase d).map (firstDigit s) := hx
    obtain ⟨c,hc,rfl⟩ := mem_map.mp hx'
    obtain ⟨v,_,hv⟩ := mem_map.mp hxd
    have hdc : d = c := (List.cons.inj hv).1
    exact (mem_erase.mp hc).1 hdc.symm
  rw [filter_union, hf, valid_map d S hS, card_union_of_disjoint hd]
  simp [f, card_erase_of_mem]

private theorem insert_front (d : Digit) (s : Word) : d :: s ∈ insertions s := by
  cases s with
  | nil => exact mem_map.mpr ⟨d, mem_univ _, rfl⟩
  | cons c cs => exact mem_union_left _ (mem_map.mpr ⟨d, mem_univ _, rfl⟩)

private theorem insert_step (d : Digit) (s : Word) (hs : canonical s) (hlen : 3 ≤ s.length) :
    ((insertions (d :: s)).filter canonical).card =
      2 + ((insertions s).filter canonical).card := by
  have hfront :
      univ.map (firstDigit (d :: s)) =
      insert (d :: d :: s) ((univ.erase d).map (firstDigit (d :: s))) := by
    symm
    rw [show (d :: d :: s) = firstDigit (d :: s) d by rfl, ← map_insert, insert_erase (mem_univ d)]
  rw [insertions, hfront, insert_union, insert_eq_of_mem]
  · exact add_front d (d::s) (insertions s)
      ((canonical_pref d s (by omega)).mpr hs) (by simp; omega)
      (by intro v hv; have h := insert_length hv; omega)
  · exact mem_union_right _ (mem_map.mpr ⟨d::s,insert_front d s,rfl⟩)

private theorem sub_step (d : Digit) (s : Word) (hs : canonical s) (hlen : 3 ≤ s.length) :
    ((substitutions (d :: s)).filter canonical).card =
      2 + ((substitutions s).filter canonical).card := by
  rw [substitutions]
  exact add_front d s (substitutions s) hs (by omega)
    (by intro v hv; have h := sub_length hv; omega)

private theorem count_step (d : Digit) (s : Word) (hs : canonical s) (hlen : 3 ≤ s.length) :
    count (d :: s) = count s + if s.head? = some d then 4 else 5 := by
  unfold count
  rw [delete_step d s hs hlen, insert_step d s hs hlen, sub_step d s hs hlen]
  split <;> omega


private theorem canonical_numeral (n : ℕ) (hn : n ≠ 0) : canonical (numeral n) := by
  have hne : Nat.digits 3 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  simp only [numeral, if_neg hn, canonical]
  refine ⟨?_,Or.inr ?_⟩
  · intro he
    exact hne (by simpa using he)
  rw [List.getLast?_map, List.getLast?_eq_some_getLast hne, Option.map_some]
  intro he
  have hval : ((Nat.digits 3 n).getLast hne) % 3 = 0 := congrArg Fin.val (Option.some.inj he)
  have hmem := List.mem_of_mem_getLast? (List.getLast_mem_getLast? hne)
  have hlt := Nat.digits_lt_base (by decide : 1 < 3) hmem
  rw [Nat.mod_eq_of_lt hlt] at hval
  exact Nat.getLast_digit_ne_zero 3 hn hval

private theorem numeral_add (n : ℕ) (hn : n ≠ 0) (d : Digit) :
    numeral (3*n + (d:ℕ)) = d :: numeral n := by
  simp only [numeral, if_neg hn, if_neg (show 3*n + (d:ℕ) ≠ 0 by omega)]
  rw [Nat.add_comm (3*n) (d:ℕ), Nat.digits_add 3 (by decide) d n d.isLt (Or.inr hn), List.map_cons]
  have h : trit (d:ℕ) = d := Fin.ext (Nat.mod_eq_of_lt d.isLt)
  rw [h]

theorem main (m : ℕ) (hm : 3 ≤ m) (d e : Digit) :
    a (9*m + 3*(d:ℕ) + (e:ℕ)) =
      a (3*m + (d:ℕ)) + if d = e then 4 else 5 := by
  let n := 3*m + (d:ℕ)
  have hn : 9 ≤ n := by dsimp [n]; omega
  have hlen : 3 ≤ (numeral n).length := by
    have h := (Nat.lt_digits_length_iff (b := 3) (k := 2) (by decide) n).mpr hn
    simpa [numeral, show n ≠ 0 by omega] using Nat.succ_le_of_lt h
  have hhead : (numeral n).head? = some d := by
    dsimp [n]
    rw [numeral_add m (by omega) d]
    rfl
  change a (9*m + 3*(d:ℕ) + (e:ℕ)) = a n + if d = e then 4 else 5
  rw [show 9*m + 3*(d:ℕ) + (e:ℕ) = 3*n + (e:ℕ) by dsimp [n]; omega]
  unfold a
  rw [numeral_add n (by omega) e, count_step e (numeral n) (canonical_numeral n (by omega)) hlen,
    hhead]
  simp only [Option.some_inj]

end OpenMath.A081732

theorem OMA.solution : type_of% @OMA.S_oeis_a081732.main := by
  exact OpenMath.A081732.main
