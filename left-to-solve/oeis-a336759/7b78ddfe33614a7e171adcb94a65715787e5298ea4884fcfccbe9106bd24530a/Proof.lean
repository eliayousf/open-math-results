import OMAStatements.S_oeis_a336759
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OpenMath.A336759

open Finset

open OMA.S_oeis_a336759 (repunit IsRepdigit Decomposition)

private theorem repunit_mul (l : ℕ) : 9 * repunit l = 10^l - 1 := by
  induction l with
  | zero => decide
  | succ l ih =>
    rw [repunit, pow_succ]
    have hp : 0 < (10 : ℕ)^l := pow_pos (by decide) _
    omega

private def nine (i : ℕ) : ℕ := 9 * repunit (i+1)
private theorem nine_formula (i : ℕ) : nine i = 10^(i+1) - 1 := repunit_mul _

private theorem nine_inj : Function.Injective nine := by
  intro i j hij
  rw [nine_formula, nine_formula] at hij
  have hi : 0 < (10 : ℕ)^(i+1) := pow_pos (by decide) _
  have hj : 0 < (10 : ℕ)^(j+1) := pow_pos (by decide) _
  have hp : (10 : ℕ)^(i+1) = 10^(j+1) := by omega
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · exact (ne_of_lt (Nat.pow_lt_pow_right (by decide) (show i+1 < j+1 by omega))) hp
  · exact (ne_of_gt (Nat.pow_lt_pow_right (by decide) (show j+1 < i+1 by omega))) hp

private theorem nine_sum_bound (h : ℕ) :
    ∑ i ∈ range h, nine i < 2 * 10^h := by
  induction h with
  | zero => decide
  | succ h ih =>
    rw [sum_range_succ, nine_formula, pow_succ]
    have hp : 0 < (10 : ℕ)^h := pow_pos (by decide) _
    omega

private theorem nine_super (h : ℕ) : ∑ i ∈ range h, nine i < nine h := by
  have hs := nine_sum_bound h
  rw [nine_formula, pow_succ]
  have hp : 0 < (10 : ℕ)^h := pow_pos (by decide) _
  omega

private theorem subset_range_small {s : Finset ℕ} {h : ℕ}
    (hs : s ⊆ range (h+1)) (hh : h ∉ s) : s ⊆ range h := by
  intro x hx
  have hl := mem_range.mp (hs hx)
  apply mem_range.mpr
  by_contra! hge
  have he : x = h := by omega
  exact hh (he ▸ hx)

private theorem subset_erase_small {s : Finset ℕ} {h : ℕ}
    (hs : s ⊆ range (h+1)) : s.erase h ⊆ range h := by
  apply subset_range_small
  · exact erase_subset _ _ |>.trans hs
  · simp

private theorem sum_nines_inj (h : ℕ) (s t : Finset ℕ) (hs : s ⊆ range h) (ht : t ⊆ range h)
    (he : (∑ i ∈ s,nine i) = ∑ i ∈ t,nine i) : s = t := by
  induction h generalizing s t with
  | zero =>
    simp only [range_zero, subset_empty] at hs ht
    exact hs.trans ht.symm
  | succ h ih =>
    by_cases hhs : h ∈ s
    · by_cases hht : h ∈ t
      · have heS := sum_erase_add s nine hhs
        have heT := sum_erase_add t nine hht
        have heE : (∑ i ∈ s.erase h,nine i) = ∑ i ∈ t.erase h,nine i := by omega
        have hst := ih _ _ (subset_erase_small hs) (subset_erase_small ht) heE
        rw [← insert_erase hhs, hst, insert_erase hht]
      · have hlarge : nine h ≤ ∑ i ∈ s,nine i :=
          single_le_sum (fun _ _ => Nat.zero_le _) hhs
        have hsmall := (sum_le_sum_of_subset (f := nine) (subset_range_small ht hht)).trans_lt
          (nine_super h)
        omega
    · by_cases hht : h ∈ t
      · have hlarge : nine h ≤ ∑ i ∈ t,nine i :=
          single_le_sum (fun _ _ => Nat.zero_le _) hht
        have hsmall := (sum_le_sum_of_subset (f := nine) (subset_range_small hs hhs)).trans_lt
          (nine_super h)
        omega
      · exact ih _ _ (subset_range_small hs hhs) (subset_range_small ht hht) he

private def longSums (h : ℕ) : Finset ℕ :=
  (range h).powerset.image fun s => ∑ i ∈ s, nine i

private theorem long_card (h : ℕ) : (longSums h).card = 2^h := by
  unfold longSums
  rw [card_image_of_injOn, card_powerset, card_range]
  intro s hs t ht he
  exact sum_nines_inj h s t (mem_powerset.mp hs) (mem_powerset.mp ht) he

private theorem long_decomp (h m : ℕ) (hm : m ∈ longSums h) :
    m < 10^(h+1) ∧ ∃ s : Finset ℕ, Decomposition m s := by
  obtain ⟨s,hs,rfl⟩ := mem_image.mp hm
  constructor
  · have hb := (sum_le_sum_of_subset (f := nine) (mem_powerset.mp hs)).trans_lt
      (nine_sum_bound h)
    rw [pow_succ]
    omega
  · refine ⟨s.image nine, ?_, ?_⟩
    · intro d hd
      obtain ⟨i,_,rfl⟩ := mem_image.mp hd
      exact ⟨9,i+1,by decide,by decide,by omega,rfl⟩
    · exact sum_image (fun _ _ _ _ hh => nine_inj hh)

private def pool (h : ℕ) : Finset ℕ :=
  ((Icc 1 9) ×ˢ (Icc 1 h)).image fun p => p.1 * repunit p.2

private theorem pool_card (h : ℕ) : (pool h).card ≤ 9*h := by
  unfold pool
  calc
    _ ≤ ((Icc 1 9) ×ˢ (Icc 1 h)).card := card_image_le
    _ = _ := by simp [Nat.card_Icc]

private theorem in_pool (h x : ℕ) (hx : x < 10^h) (hr : IsRepdigit x) :
    x ∈ pool h := by
  obtain ⟨d,l,hd1,hd9,hl1,rfl⟩ := hr
  have hl : l ≤ h := by
    by_contra! hlt
    have h1 : (10 : ℕ)^(h+1) ≤ 10^l :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : repunit l ≤ d * repunit l := by
      simpa only [one_mul] using Nat.mul_le_mul_right (repunit l) hd1
    have h3 : 9*repunit l ≤ 9*(d * repunit l) := Nat.mul_le_mul_left 9 h2
    rw [repunit_mul l] at h3
    rw [pow_succ] at h1
    omega
  exact mem_image.mpr ⟨(d,l), mem_product.mpr ⟨mem_Icc.mpr ⟨hd1,hd9⟩,
    mem_Icc.mpr ⟨hl1,hl⟩⟩, rfl⟩

private def shortSets (h n : ℕ) : Finset (Finset ℕ) :=
  (range n).biUnion fun j => (pool (h+1)).powersetCard j

private def shortSums (h n : ℕ) : Finset ℕ :=
  (shortSets h n).image fun s => ∑ i ∈ s, i

private theorem short_card (h n : ℕ) : (shortSums h n).card ≤ n*(9*(h+1))^n := by
  apply card_image_le.trans
  unfold shortSets
  have hp := card_biUnion_le_card_mul (range n)
    (fun j => (pool (h+1)).powersetCard j) ((9*(h+1))^n) ?_
  · simpa using hp
  · intro j hj
    rw [card_powersetCard]
    exact (Nat.choose_le_pow _ _).trans
      ((Nat.pow_le_pow_left (pool_card (h+1)) j).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt (mem_range.mp hj))))

private theorem short_mem (h n m : ℕ) (hm : m < 10^(h+1))
    (s : Finset ℕ) (hs : Decomposition m s) (hc : s.card < n) :
    m ∈ shortSums h n := by
  have hsubset : s ⊆ pool (h+1) := by
    intro x hx
    have hxm : x ≤ m := by
      rw [← hs.2]
      exact single_le_sum (f := fun i : ℕ => i) (fun _ _ => Nat.zero_le _) hx
    exact in_pool _ _ (hxm.trans_lt hm) (hs.1 x hx)
  refine mem_image.mpr ⟨s, mem_biUnion.mpr ⟨s.card, mem_range.mpr hc,
    mem_powersetCard.mpr ⟨hsubset, rfl⟩⟩, hs.2⟩

private theorem short_zero (h n : ℕ) (hn : 1 ≤ n) : 0 ∈ shortSums h n := by
  refine mem_image.mpr ⟨∅, mem_biUnion.mpr ⟨0, mem_range.mpr (by omega),
    mem_powersetCard.mpr ⟨empty_subset _, by simp⟩⟩, by simp⟩

private theorem sq_le_two_pow (m : ℕ) (hm : 4 ≤ m) : m^2 ≤ 2^m := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, m = t+4 := ⟨m-4, by omega⟩
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show t+1+4=(t+4)+1 by omega, pow_succ (2 : ℕ) (t+4)]
    calc
      (t+4+1)^2 ≤ 2*(t+4)^2 := by nlinarith
      _ ≤ _ := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left 2 (ih (by omega))

private theorem explicit_gap (n : ℕ) :
    ∃ h : ℕ, n * (9*(h+1))^n < 2^h := by
  let m := 2*n+10
  let h := 2^m
  have hh : 0 < h := pow_pos (by decide) _
  have hs : m^2 ≤ h := sq_le_two_pow m (by dsimp [m]; omega)
  have hg : (m+6)*n < h := by
    apply lt_of_lt_of_le _ hs
    dsimp [m]
    nlinarith
  have hsmall : 9*(h+1) ≤ 2^(m+5) := by
    rw [pow_add, show (2 : ℕ)^5=32 by decide]
    change 9*(h+1) ≤ h*32
    omega
  refine ⟨h,?_⟩
  calc
    _ ≤ 2^n * (2^(m+5))^n :=
      Nat.mul_le_mul n.lt_two_pow_self.le (Nat.pow_le_pow_left hsmall _)
    _ = 2^((m+6)*n) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    _ < _ := Nat.pow_lt_pow_right (by decide) hg

theorem main : ∀ n ≥ 1,
    ∃ m : ℕ, 0 < m ∧ (∃ s : Finset ℕ, Decomposition m s) ∧
      ∀ s : Finset ℕ, Decomposition m s → n ≤ s.card := by
  intro n hn
  obtain ⟨h,hgap⟩ := explicit_gap n
  have hcard : (shortSums h n).card < (longSums h).card :=
    (short_card h n).trans_lt (by rw [long_card]; exact hgap)
  obtain ⟨m,hm,hs⟩ := exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨hbound, hrep⟩ := long_decomp h m hm
  refine ⟨m, ?_, hrep, ?_⟩
  · by_contra! hnp
    have hm0 : m = 0 := by omega
    exact hs (hm0.symm ▸ short_zero h n hn)
  · intro s hdec
    by_contra! hsmall
    exact hs (short_mem h n m hbound s hdec hsmall)

end OpenMath.A336759

theorem OMA.solution : type_of% @OMA.S_oeis_a336759.main := OpenMath.A336759.main
