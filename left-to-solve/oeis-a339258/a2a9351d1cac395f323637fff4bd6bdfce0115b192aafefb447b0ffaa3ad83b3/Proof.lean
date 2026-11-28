import OMAStatements.S_oeis_a339258

namespace OMA.S_oeis_a339258

open Finset

private theorem copies_le {d j : ℕ} {s : Multiset ℕ} (h : j ≤ s.count d) :
    Multiset.replicate j d ≤ s := by
  apply Multiset.le_iff_count.mpr
  intro e
  by_cases he : d = e
  · subst e
    simpa using h
  · simp [Multiset.count_replicate, he]

private theorem copies_sum (j d : ℕ) : (Multiset.replicate j d).sum = j * d := by
  simp [Multiset.sum_replicate]

private theorem copies_mass {n d : ℕ} (p : Nat.Partition n) : p.parts.count d * d ≤ n := by
  have hrep : Multiset.replicate (p.parts.count d) d ≤ p.parts := copies_le le_rfl
  have he := congrArg Multiset.sum (tsub_add_cancel_of_le hrep)
  simp only [Multiset.sum_add, copies_sum, p.parts_sum] at he
  omega

private theorem marked_count {n d : ℕ} (p : Nat.Partition n) (hd : 0 < d) :
    ((range n).filter (fun k => d ∣ n - k ∧ n - k ≤ p.parts.count d * d)).card =
      p.parts.count d := by
  conv_rhs => rw [← card_range (p.parts.count d)]
  symm
  refine card_bij (fun j _ => n - (j + 1) * d) ?_ ?_ ?_
  · intro j hj
    have hj' : j + 1 ≤ p.parts.count d := Nat.succ_le_of_lt (mem_range.mp hj)
    have hm := Nat.mul_le_mul_right d hj'
    have hb := copies_mass (d := d) p
    have hp : 0 < (j + 1) * d := by positivity
    have he : n - (n - (j + 1) * d) = (j + 1) * d := by omega
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩
    rw [he]
    exact ⟨⟨j + 1, Nat.mul_comm _ _⟩, hm⟩
  · intro i hi j hj h
    have hi' : i + 1 ≤ p.parts.count d := Nat.succ_le_of_lt (mem_range.mp hi)
    have hj' : j + 1 ≤ p.parts.count d := Nat.succ_le_of_lt (mem_range.mp hj)
    have ha := Nat.mul_le_mul_right d hi'
    have hb := Nat.mul_le_mul_right d hj'
    have hc := copies_mass (d := d) p
    have hm : (i + 1) * d = (j + 1) * d := by omega
    have he : i + 1 = j + 1 := by
      simpa only [Nat.mul_div_cancel _ hd] using congrArg (fun m : ℕ => m / d) hm
    omega
  · intro k hk
    obtain ⟨hk, hkd, hkc⟩ := mem_filter.mp hk
    have hk' : k < n := mem_range.mp hk
    let j := (n - k) / d
    have he : j * d = n - k := Nat.div_mul_cancel hkd
    have hj : 0 < j := by
      by_contra! h
      simp [Nat.eq_zero_of_le_zero h] at he
      omega
    have hj' : j ≤ p.parts.count d := by
      calc
        j ≤ (p.parts.count d * d) / d := Nat.div_le_div_right hkc
        _ = p.parts.count d := Nat.mul_div_cancel _ hd
    refine ⟨j - 1, mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_add_cancel (show 1 ≤ j by omega), he]
    omega

private theorem count_partitions {n k d : ℕ} (hk : k ≤ n) (hd : 0 < d) (hdiv : d ∣ n - k) :
    ((univ : Finset (Nat.Partition n)).filter (fun p => n - k ≤ p.parts.count d * d)).card =
      A000041 k := by
  classical
  let j := (n - k) / d
  let r := Multiset.replicate j d
  have hr : r.sum = n - k := by
    rw [show r.sum = j * d from copies_sum j d]
    exact Nat.div_mul_cancel hdiv
  let P := {p : Nat.Partition n // n - k ≤ p.parts.count d * d}
  have hsub (p : P) : r ≤ p.val.parts := by
    apply copies_le
    exact Nat.div_le_of_le_mul (p.property.trans_eq (Nat.mul_comm _ _))
  let cut (p : P) : Nat.Partition k :=
    ⟨p.val.parts - r,
      fun {_} h => p.val.parts_pos (Multiset.mem_of_le tsub_le_self h),
      by
        have he := congrArg Multiset.sum (tsub_add_cancel_of_le (hsub p))
        simp only [Multiset.sum_add, hr, p.val.parts_sum] at he
        omega⟩
  let glueParts (p : Nat.Partition k) : Nat.Partition n :=
    ⟨p.parts + r,
      fun {_} h => by
        rcases Multiset.mem_add.mp h with h | h
        · exact p.parts_pos h
        · exact (Multiset.mem_replicate.mp h).2.symm ▸ hd,
      by simp only [Multiset.sum_add, p.parts_sum, hr]; omega⟩
  let glue (p : Nat.Partition k) : P := ⟨glueParts p, by
    change n - k ≤ (p.parts + r).count d * d
    simp only [Multiset.count_add, r, Multiset.count_replicate_self, Nat.add_mul]
    have he : j * d = n - k := Nat.div_mul_cancel hdiv
    omega⟩
  let e : P ≃ Nat.Partition k :=
    ⟨cut, glue,
      fun p => Subtype.ext (Nat.Partition.ext (tsub_add_cancel_of_le (hsub p))),
      fun p => Nat.Partition.ext (add_tsub_cancel_right p.parts r)⟩
  change _ = Fintype.card (Nat.Partition k)
  rw [← Fintype.card_congr e]
  exact (Fintype.card_of_subtype _ (fun p => by simp)).symm

private theorem row_sum (n : ℕ) :
    (row n).sum = ∑ k ∈ range n, A000041 k * (n - k).divisors.card := by
  have h (l : List ℕ) :
      (l.flatMap (fun k => List.replicate (A000041 k) (n - k).divisors.card)).sum =
        (l.map (fun k => A000041 k * (n - k).divisors.card)).sum := by
    induction l with
    | nil => rfl
    | cons k l ih => simp [List.sum_replicate, ih]
  unfold row rowA176206
  rw [List.map_flatMap]
  simp_rw [List.map_replicate]
  rw [h, sum_eq_multiset_sum]
  rfl

end OMA.S_oeis_a339258

open Finset OMA.S_oeis_a339258 in
theorem OMA.solution : type_of% @OMA.S_oeis_a339258.main := by
  intro n _
  rw [row_sum]
  unfold A006128
  calc
    _ = ∑ k ∈ range n, ∑ d ∈ Icc 1 n, if d ∣ n - k then A000041 k else 0 := by
      apply sum_congr rfl
      intro k hk
      have hk' : k < n := mem_range.mp hk
      have hdivisors : (n - k).divisors = (Icc 1 n).filter (fun d => d ∣ n - k) := by
        ext d
        constructor
        · intro hd
          have hdvd := Nat.dvd_of_mem_divisors hd
          have hpos := Nat.pos_of_mem_divisors hd
          have hle := Nat.le_of_dvd (show 0 < n - k by omega) hdvd
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpos, by omega⟩, hdvd⟩
        · intro hd
          exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, by omega⟩
      rw [← sum_filter, ← hdivisors]
      simp [Nat.mul_comm]
    _ = ∑ d ∈ Icc 1 n, ∑ k ∈ range n, if d ∣ n - k then A000041 k else 0 := sum_comm
    _ = ∑ d ∈ Icc 1 n, ∑ p : Nat.Partition n, p.parts.count d := by
      apply sum_congr rfl
      intro d hd
      have hd' : 0 < d := (mem_Icc.mp hd).1
      have he : ∑ p : Nat.Partition n, p.parts.count d =
          ∑ p : Nat.Partition n, ∑ k ∈ range n, if
            d ∣ n - k ∧ n - k ≤ p.parts.count d * d then 1 else 0 := by
        apply sum_congr rfl
        intro p _
        rw [sum_boole]
        exact (marked_count p hd').symm
      rw [he, sum_comm]
      apply sum_congr rfl
      intro k hk
      by_cases hdiv : d ∣ n - k
      · simp only [hdiv, if_true, true_and, sum_boole]
        exact (count_partitions (mem_range.mp hk).le hd' hdiv).symm
      · simp [hdiv]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      exact Multiset.sum_count_eq_card
        (fun d hd => mem_Icc.mpr ⟨p.parts_pos hd, Nat.Partition.le_of_mem_parts hd⟩)
