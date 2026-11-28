import OMAStatements.S_oeis_a082477

namespace OMA.S_oeis_a082477

open Filter Topology Finset

private abbrev proper (n d : ℕ) : Prop :=
  d < n ∧ d ∣ n ∧ d + 1 ∣ n + 1

private theorem proper_iff {n d : ℕ} (hd : 0 < d) :
    proper n d ↔ ∃ j : ℕ, 0 < j ∧ n = d + j * (d * (d + 1)) := by
  constructor
  · rintro ⟨hlt, hfirst, hsecond⟩
    have hdvd := Nat.dvd_sub hfirst (dvd_refl d)
    have hdvd' := Nat.dvd_sub hsecond (dvd_refl (d + 1))
    rw [show n + 1 - (d + 1) = n - d by omega] at hdvd'
    have hc : d.Coprime (d + 1) := by
      rw [Nat.add_comm d 1, Nat.coprime_add_self_right]
      simp
    obtain ⟨j, hj⟩ := hc.mul_dvd_of_dvd_of_dvd hdvd hdvd'
    have hp : 0 < j := by
      by_contra! h
      simp [Nat.eq_zero_of_le_zero h] at hj
      omega
    rw [Nat.mul_comm] at hj
    exact ⟨j, hp, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    have hpos : 0 < j * (d * (d + 1)) := by positivity
    refine ⟨by omega, dvd_add (dvd_refl _) ⟨j * (d + 1), by ring⟩, ?_⟩
    rw [show d + j * (d * (d + 1)) + 1 = (d + 1) + j * (d * (d + 1)) by omega]
    exact dvd_add (dvd_refl _) ⟨j * d, by ring⟩

private theorem term_as_sum {n N : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    (term n : ℝ) = 1 + ∑ j ∈ range N, if proper n (j + 1) then 1 else 0 := by
  let ds := n.divisors.filter (fun d => d + 1 ∣ n + 1)
  have hmem : n ∈ ds := by simp [ds, Nat.mem_divisors, hn.ne']
  have hcard : ((range N).filter (fun j => proper n (j + 1))).card = (ds.erase n).card := by
    refine card_bij' (fun j _ => j + 1) (fun d _ => d - 1) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [mem_filter, mem_range] at hj
      apply mem_erase.mpr
      refine ⟨hj.2.1.ne, ?_⟩
      change j + 1 ∈ n.divisors.filter (fun d => d + 1 ∣ n + 1)
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hj.2.2.1, hn.ne'⟩, hj.2.2.2⟩
    · intro d hd
      obtain ⟨hne, hmem'⟩ := mem_erase.mp hd
      obtain ⟨hdiv, hstep⟩ := mem_filter.mp hmem'
      have hpos := Nat.pos_of_mem_divisors hdiv
      have hlt := lt_of_le_of_ne (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hdiv)) hne
      have he : d - 1 + 1 = d := by omega
      change d - 1 ∈ (range N).filter (fun j => proper n (j + 1))
      refine mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩
      rw [he]
      exact ⟨hlt, Nat.dvd_of_mem_divisors hdiv, hstep⟩
    · intro j _
      omega
    · intro d hd
      have hpos := Nat.pos_of_mem_divisors (mem_filter.mp (mem_erase.mp hd).2).1
      change d - 1 + 1 = d
      omega
  rw [sum_boole, hcard]
  change (ds.card : ℝ) = 1 + ((ds.erase n).card : ℝ)
  have hpos : 0 < ds.card := card_pos.mpr ⟨n, hmem⟩
  rw [card_erase_of_mem hmem, Nat.cast_sub (show 1 ≤ ds.card by omega), Nat.cast_one]
  ring

private theorem proper_count (N d : ℕ) (hd : 0 < d) :
    ((range N).filter (fun i => proper (i + 1) d)).card = (N - d) / (d * (d + 1)) := by
  let q := d * (d + 1)
  have hq : 0 < q := by dsimp [q]; positivity
  rw [← card_range ((N - d) / q)]
  symm
  apply card_bij (fun j _ => d + (j + 1) * q - 1)
  · intro j hj
    have hle : (j + 1) * q ≤ N - d :=
      (Nat.le_div_iff_mul_le hq).mp (Nat.succ_le_of_lt (mem_range.mp hj))
    have hpos : 0 < (j + 1) * q := by positivity
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), (proper_iff hd).mpr ?_⟩
    have he : d + (j + 1) * q - 1 + 1 = d + (j + 1) * q := by omega
    exact ⟨j + 1, by omega, he⟩
  · intro j _ k _ he
    have hmul : (j + 1) * q = (k + 1) * q := by omega
    have hcancel : j + 1 = k + 1 := by
      simpa only [Nat.mul_div_cancel _ hq] using congrArg (fun x : ℕ => x / q) hmul
    omega
  · intro i hi
    obtain ⟨hil, hip⟩ := mem_filter.mp hi
    obtain ⟨j, hj, he⟩ := (proper_iff hd).mp hip
    change i + 1 = d + j * q at he
    have hle : j * q ≤ N - d := by have := mem_range.mp hil; omega
    have hj' := (Nat.le_div_iff_mul_le hq).mpr hle
    refine ⟨j - 1, mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_add_cancel (show 1 ≤ j by omega)]
    omega

private def modulus (j : ℕ) : ℕ := (j + 1) * (j + 2)

private noncomputable def weight (j : ℕ) : ℝ := (modulus j : ℝ)⁻¹

private noncomputable def portion (N j : ℕ) : ℝ :=
  (((N - (j + 1)) / modulus j : ℕ) : ℝ) / (N : ℝ)

private theorem weight_hasSum : HasSum weight 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => by unfold weight; positivity) 1]
  let invShift (j : ℕ) : ℝ := ((j : ℝ) + 1)⁻¹
  have he (j : ℕ) : weight j = invShift j - invShift (j + 1) := by
    dsimp [weight, invShift, modulus]
    push_cast
    have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [he, sum_range_sub']
  have hnat : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => by linarith) tendsto_natCast_atTop_atTop
  have hi : Tendsto invShift atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hnat
  simpa [invShift] using (tendsto_const_nhds (x := (1 : ℝ))).sub hi

private theorem portion_le_weight (N j : ℕ) : portion N j ≤ weight j := by
  by_cases hN : N = 0
  · subst N; simp [portion, weight]
  have hn : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have hq : 0 < (modulus j : ℝ) := by unfold modulus; positivity
  have hdiv : ((((N - (j + 1)) / modulus j : ℕ) : ℝ) * modulus j ≤ (N : ℝ)) := by
    exact_mod_cast (Nat.div_mul_le_self (N - (j + 1)) (modulus j)).trans (Nat.sub_le _ _)
  unfold portion weight
  apply (div_le_iff₀ hn).2
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hq).2 hdiv

private theorem portion_tendsto (j : ℕ) : Tendsto (fun N : ℕ => portion N j) atTop (𝓝 (weight j)) := by
  let C : ℝ := ((j + 1 : ℕ) + modulus j : ℕ) / (modulus j : ℝ)
  have hqN : 0 < modulus j := by unfold modulus; positivity
  have hq : 0 < (modulus j : ℝ) := by exact_mod_cast hqN
  have hi : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun N : ℕ => weight j - C / (N : ℝ))
    (by simpa using (tendsto_const_nhds (x := weight j)).sub hi)
    tendsto_const_nhds ?_ (Eventually.of_forall fun N => portion_le_weight N j)
  filter_upwards [eventually_ge_atTop (j + 1)] with N hn
  have hnR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hdivision :
      ((N - (j + 1) : ℕ) : ℝ) <
        (((N - (j + 1)) / modulus j : ℕ) : ℝ) * (modulus j : ℝ) + (modulus j : ℝ) := by
    exact_mod_cast (Nat.lt_div_mul_add (a := N - (j + 1)) hqN)
  rw [Nat.cast_sub hn] at hdivision
  unfold portion
  apply (le_div_iff₀ hnR).2
  calc
    (weight j - C / (N : ℝ)) * (N : ℝ) =
        ((N : ℝ) - ((j + 1 : ℕ) : ℝ) - (modulus j : ℝ)) / (modulus j : ℝ) := by
      dsimp [weight, C]
      push_cast
      field_simp
      ring
    _ ≤ (((N - (j + 1)) / modulus j : ℕ) : ℝ) := by
      apply (div_le_iff₀ hq).2
      linarith only [hdivision]

private theorem mean_eventually :
    (fun N : ℕ => (∑ i ∈ range N, (term (i + 1) : ℝ)) / (N : ℝ))
      =ᶠ[atTop] (fun N : ℕ => 1 + ∑' j, portion N j) := by
  filter_upwards [eventually_ge_atTop 1] with N hn
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs : ∑ i ∈ range N, (term (i + 1) : ℝ) =
      ∑ i ∈ range N, (1 + ∑ j ∈ range N, if proper (i + 1) (j + 1) then 1 else 0) := by
    apply sum_congr rfl
    intro i hi
    exact term_as_sum (by omega) (Nat.succ_le_of_lt (mem_range.mp hi))
  rw [hs, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one, sum_comm,
    add_div, div_self hN]
  have hfinite : (∑' j, portion N j) = ∑ j ∈ range N, portion N j :=
    tsum_eq_sum fun j hj => by
      have hj' : N ≤ j + 1 := by simp only [mem_range, not_lt] at hj; omega
      simp [portion, Nat.sub_eq_zero_of_le hj']
  rw [hfinite, sum_div]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [sum_boole, proper_count N (j + 1) (by omega)]
  rfl

end OMA.S_oeis_a082477

open Filter Topology OMA.S_oeis_a082477 in
theorem OMA.solution : type_of% @OMA.S_oeis_a082477.main := by
  have hpsum := tendsto_tsum_of_dominated_convergence weight_hasSum.summable portion_tendsto
    (Eventually.of_forall fun N j => by
      have hnonneg : 0 ≤ portion N j := by unfold portion; positivity
      rw [Real.norm_of_nonneg hnonneg]
      exact portion_le_weight N j)
  rw [weight_hasSum.tsum_eq] at hpsum
  have htotal := (tendsto_const_nhds (x := (1 : ℝ))).add hpsum
  have h := htotal.congr' mean_eventually.symm
  norm_num at h
  exact h
