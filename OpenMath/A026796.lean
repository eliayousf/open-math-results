import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-! Beck's partition identity in OEIS A026796, with its corrected shift. -/

namespace OpenMath.A026796

open Multiset

abbrev LeastThree (n : ℕ) :=
  {p : Nat.Partition n // 3 ∈ p.parts ∧ ∀ x ∈ p.parts, 3 ≤ x}

abbrev Balanced (n : ℕ) :=
  {p : Nat.Partition n // 2 * p.parts.count 1 = p.parts.card}

instance (n : ℕ) : Fintype (LeastThree n) := by
  unfold LeastThree
  infer_instance

instance (n : ℕ) : Fintype (Balanced n) := by
  unfold Balanced
  infer_instance

def a (n : ℕ) : ℕ := Fintype.card (LeastThree n)

def b (n : ℕ) : ℕ := Fintype.card (Balanced n)

private def nonOnes (s : Multiset ℕ) : Multiset ℕ := s.filter (· ≠ 1)

private theorem ones_add_nonOnes (s : Multiset ℕ) :
    replicate (s.count 1) 1 + nonOnes s = s := by
  rw [← filter_eq']
  exact filter_add_not (· = 1) s

private theorem card_nonOnes {n : ℕ} (p : Balanced n) :
    (nonOnes p.1.parts).card = p.1.parts.count 1 := by
  have hcard := congrArg Multiset.card (ones_add_nonOnes p.1.parts)
  have hb := p.2
  simp only [card_add, card_replicate] at hcard
  omega

private theorem sum_nonOnes {n : ℕ} (p : Balanced n) :
    (nonOnes p.1.parts).sum + (nonOnes p.1.parts).card = n := by
  have hsum := congrArg Multiset.sum (ones_add_nonOnes p.1.parts)
  simp only [sum_add, sum_replicate, smul_eq_mul, Nat.mul_one, p.1.parts_sum] at hsum
  rw [card_nonOnes p]
  omega

private theorem sum_increment (s : Multiset ℕ) :
    (s.map (· + 1)).sum = s.sum + s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih => simp only [map_cons, sum_cons, card_cons, ih]; omega

private theorem sum_decrement (s : Multiset ℕ) (h : ∀ x ∈ s, 1 ≤ x) :
    (s.map (· - 1)).sum + s.card = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    have hx := h x (mem_cons_self _ _)
    have hs := ih (fun y hy => h y (mem_cons_of_mem hy))
    simp only [map_cons, sum_cons, card_cons]
    omega

private def pairOnes (n : ℕ) (p : Balanced n) : LeastThree (n + 3) := by
  let rest := nonOnes p.1.parts
  have hmin : ∀ x ∈ 3 ::ₘ rest.map (· + 1), 3 ≤ x := by
    intro x hx
    rcases mem_cons.mp hx with rfl | hx
    · rfl
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    rw [show rest = p.1.parts.filter (· ≠ 1) by rfl, mem_filter] at hy
    have hypos := p.1.parts_pos hy.1
    omega
  refine ⟨⟨3 ::ₘ rest.map (· + 1), fun hx => ?_, ?_⟩, mem_cons_self _ _, hmin⟩
  · have := hmin _ hx
    omega
  · change (3 ::ₘ rest.map (· + 1)).sum = n + 3
    rw [sum_cons, sum_increment, show rest.sum + rest.card = n from sum_nonOnes p, Nat.add_comm]

private theorem erase_three_sum {n : ℕ} (p : LeastThree n) :
    3 + (p.1.parts.erase 3).sum = n := by
  simpa only [sum_cons, p.1.parts_sum] using congrArg Multiset.sum (cons_erase p.2.1)

private def unpairOnes (n : ℕ) (p : LeastThree (n + 3)) : Balanced n := by
  let rest := p.1.parts.erase 3
  let decreased := rest.map (· - 1)
  have hmin : ∀ x ∈ rest, 3 ≤ x := fun x hx => p.2.2 x (p.1.parts.erase_subset 3 hx)
  have hdmin : ∀ x ∈ decreased, 2 ≤ x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    have := hmin y hy
    omega
  have hsum : rest.sum = n := by
    have h : 3 + rest.sum = n + 3 := erase_three_sum p
    omega
  refine ⟨⟨decreased + replicate rest.card 1, ?_, ?_⟩, ?_⟩
  · intro x hx
    rcases mem_add.mp hx with hx | hx
    · have := hdmin x hx
      omega
    · exact eq_of_mem_replicate hx ▸ Nat.one_pos
  · have h := sum_decrement rest (fun x hx => Nat.le_trans (by decide) (hmin x hx))
    simpa only [sum_add, sum_replicate, smul_eq_mul, Nat.mul_one, decreased] using h.trans hsum
  · have hzero : decreased.count 1 = 0 := by
      apply count_eq_zero_of_notMem
      intro h
      have := hdmin 1 h
      omega
    simp [hzero, decreased, two_mul]

/-- Merge each one with a non-one part and add one occurrence of three. -/
def partitionEquiv (n : ℕ) : Balanced n ≃ LeastThree (n + 3) where
  toFun := pairOnes n
  invFun := unpairOnes n
  left_inv p := by
    apply Subtype.ext
    apply Nat.Partition.ext
    change (((3 ::ₘ (nonOnes p.1.parts).map (· + 1)).erase 3).map (· - 1)) +
      replicate ((3 ::ₘ (nonOnes p.1.parts).map (· + 1)).erase 3).card 1 = p.1.parts
    rw [erase_cons_head, map_map, card_map]
    simp only [Function.comp_apply, Nat.add_sub_cancel, map_id']
    rw [card_nonOnes p, add_comm, ones_add_nonOnes]
  right_inv p := by
    apply Subtype.ext
    apply Nat.Partition.ext
    let rest := p.1.parts.erase 3
    let decreased := rest.map (· - 1)
    have hmin : ∀ x ∈ rest, 3 ≤ x := fun x hx => p.2.2 x (p.1.parts.erase_subset 3 hx)
    change 3 ::ₘ (nonOnes (decreased + replicate rest.card 1)).map (· + 1) = p.1.parts
    have hones : (replicate rest.card (1 : ℕ)).filter (· ≠ 1) = 0 := by
      apply filter_eq_nil.2
      intro x hx
      simpa using eq_of_mem_replicate hx
    unfold nonOnes
    rw [filter_add, hones, add_zero]
    have hfilter : decreased.filter (· ≠ 1) = decreased := by
      apply filter_eq_self.2
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      have := hmin y hy
      omega
    rw [hfilter, show decreased = rest.map (· - 1) by rfl, map_map]
    have hmap : rest.map ((· + 1) ∘ (· - 1)) = rest := by
      calc
        _ = rest.map (fun x => x) := by
          apply map_congr rfl
          intro x hx
          have := hmin x hx
          simp only [Function.comp_apply]
          omega
        _ = rest := map_id' rest
    rw [hmap]
    exact cons_erase p.2.1

theorem corrected (n : ℕ) : a (n + 3) = b n :=
  Fintype.card_congr (partitionEquiv n).symm

private theorem no_partition_five : a 5 = 0 := by
  apply Fintype.card_eq_zero_iff.2
  refine ⟨fun p => ?_⟩
  have hsum := erase_three_sum p
  have hempty : p.1.parts.erase 3 = 0 := by
    apply eq_zero_of_forall_notMem
    intro x hx
    have hle := le_sum_of_mem hx
    have hmin := p.2.2 x (p.1.parts.erase_subset 3 hx)
    omega
  rw [hempty, sum_zero] at hsum
  omega

private def sixPartition : LeastThree 6 :=
  ⟨⟨3 ::ₘ ({3} : Multiset ℕ), by simp, by simp⟩, by simp⟩

private theorem one_partition_six : a 6 = 1 := by
  apply Fintype.card_eq_one_iff.2
  refine ⟨sixPartition, fun p => ?_⟩
  apply Subtype.ext
  apply Nat.Partition.ext
  have hsum : (p.1.parts.erase 3).sum = 3 := by have h := erase_three_sum p; omega
  have hrepl := (eq_replicate_card (s := p.1.parts.erase 3) (a := 3)).2 (by
    intro x hx
    have hle := le_sum_of_mem hx
    have hmin := p.2.2 x (p.1.parts.erase_subset 3 hx)
    omega)
  have h := congrArg Multiset.sum hrepl
  simp only [hsum, sum_replicate, smul_eq_mul] at h
  have hcard : (p.1.parts.erase 3).card = 1 := by omega
  rw [hcard, replicate_one] at hrepl
  change p.1.parts = 3 ::ₘ ({3} : Multiset ℕ)
  rw [← hrepl, cons_erase p.2.1]

theorem witness : a 6 = 1 ∧ b 2 = 0 := by
  exact ⟨one_partition_six, (corrected 2).symm.trans no_partition_five⟩

theorem main : ¬ ∀ n : ℕ, a (n + 4) = b n := by
  intro h
  have h2 := h 2
  change a 6 = b 2 at h2
  rw [witness.1, witness.2] at h2
  omega

end OpenMath.A026796
