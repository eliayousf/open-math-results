import OMAStatements.S_oeis_a034387

namespace A034387Proof

open OMA.S_oeis_a034387 Finset

private theorem reflect (i n : ℕ) :
    (∑ j ∈ Icc i n, (if (i+n-j).Prime then 1 else 0)) =
      ∑ p ∈ Icc i n, (if p.Prime then 1 else 0) := by
  refine sum_bij (fun j _ ↦ i+n-j) ?_ ?_ ?_ ?_
  · intro j hj
    rcases mem_Icc.mp hj with ⟨hij, hjn⟩
    apply mem_Icc.mpr
    omega
  · intro j hj k hk heq
    have hjn := (mem_Icc.mp hj).2
    have hkn := (mem_Icc.mp hk).2
    omega
  · intro p hp
    rcases mem_Icc.mp hp with ⟨hip, hpn⟩
    refine ⟨i+n-p, mem_Icc.mpr ?_, ?_⟩ <;> omega
  · intros
    rfl

private theorem weight_once (n : ℕ) : tripleCoeff n = primeSum n := by
  unfold tripleCoeff primeSum
  have rows :
      (∑ i ∈ Icc 1 n, ∑ j ∈ Icc i n, if (i+n-j).Prime then 1 else 0) =
        ∑ i ∈ Icc 1 n, ∑ p ∈ Icc 1 n, if i ≤ p then (if p.Prime then 1 else 0) else 0 := by
    apply sum_congr rfl
    intro i hi
    rw [reflect]
    have hf : ((Icc 1 n).filter (i ≤ ·)) = Icc i n := by
      ext p
      have h1i := (mem_Icc.mp hi).1
      simp only [mem_filter, mem_Icc]
      omega
    calc
      (∑ p ∈ Icc i n, if p.Prime then 1 else 0) =
          ∑ p ∈ (Icc 1 n).filter (i ≤ ·), if p.Prime then 1 else 0 := by rw [hf]
      _ = _ := by rw [sum_filter]
  rw [rows, sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [← sum_filter]
  have hf : ((Icc 1 n).filter (· ≤ p)) = Icc 1 p := by
    ext i
    have hpn := (mem_Icc.mp hp).2
    simp only [mem_filter, mem_Icc]
    omega
  rw [hf, sum_const]
  by_cases h : p.Prime <;> simp [h]

end A034387Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a034387.main := by
  ext n
  simp only [PowerSeries.coeff_mk]
  exact (A034387Proof.weight_once n).symm
