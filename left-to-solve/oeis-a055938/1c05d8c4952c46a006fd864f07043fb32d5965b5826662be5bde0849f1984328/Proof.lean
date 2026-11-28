import OMAStatements.S_oeis_a055938

namespace OMA.S_oeis_a055938

private theorem c_eq (n : ℕ) : c n = c (n / 2) + n := by
  cases n with
  | zero => rfl
  | succ n => rw [c.eq_2]

private theorem c_even (k : ℕ) : c (2 * k) = c k + 2 * k := by
  rw [c_eq (2 * k), show 2 * k / 2 = k by omega]

private theorem c_odd (k : ℕ) : c (2 * k + 1) = c k + 2 * k + 1 := by
  rw [c_eq (2 * k + 1)]
  have h : (2 * k + 1) / 2 = k := by omega
  rw [h]
  omega

private theorem c_strictMono : StrictMono c := by
  apply strictMono_nat_of_lt_succ
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n % 2 = 0
    · have hn : n = 2 * (n / 2) := by omega
      rw [show n + 1 = 2 * (n / 2) + 1 by omega, c_odd]
      conv_lhs => rw [hn, c_even]
      omega
    · let k := n / 2
      have hn : n = 2 * k + 1 := by dsimp [k]; omega
      have hkl : k < n := by omega
      have hk := ih k hkl
      rw [hn, c_odd, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, c_even]
      omega

private theorem index_le_c (k : ℕ) : k ≤ c k := by
  rw [c_eq k]
  omega

private theorem gap_outside_range {k r : ℕ} (hlo : c k < r) (hhi : r < c (k + 1)) :
    r ∉ Set.range c := by
  rintro ⟨j, rfl⟩
  exact (c_strictMono.lt_iff_lt.mp hlo).not_ge
    (Nat.lt_succ_iff.mp (c_strictMono.lt_iff_lt.mp hhi))

private theorem b_gap (n : ℕ) :
    ∃ k : ℕ, c k < n + 1 ∧ n + 1 ≤ c (k + 1) ∧ b (n + 1) = (n + 1) + 2 * k + 1 := by
  classical
  induction n with
  | zero => exact ⟨0, by simp [c.eq_1], index_le_c 1, by simp [b]⟩
  | succ n ih =>
    obtain ⟨k, hlo, hhi, hb⟩ := ih
    by_cases he : n + 1 = c (k + 1)
    · have hn : n + 1 ∉ S := fun h => h.2 ⟨k + 1, he.symm⟩
      have hnext : c (k + 1) < c (k + 1 + 1) := c_strictMono (by omega)
      refine ⟨k + 1, by omega, by omega, ?_⟩
      rw [b.eq_3, if_neg hn, hb]
      omega
    · have hn : n + 1 ∈ S := ⟨by omega, gap_outside_range hlo (by omega)⟩
      refine ⟨k, by omega, by omega, ?_⟩
      rw [b.eq_3, if_pos hn, hb]
      omega

private theorem b_mem (n : ℕ) : b (n + 1) ∈ S := by
  obtain ⟨k, hlo, hhi, hb⟩ := b_gap n
  refine ⟨by omega, gap_outside_range (k := 2 * k + 1) ?_ ?_⟩
  · rw [c_odd]; omega
  · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, c_even]; omega

private theorem b_range : Set.range (fun n : ℕ => b (n + 1)) = S := by
  apply Set.Subset.antisymm
  · rintro r ⟨n, rfl⟩
    exact b_mem n
  · intro r hr
    have hex : ∃ j : ℕ, r < c j := ⟨r + 1, (Nat.lt_succ_self r).trans_le (index_le_c _)⟩
    have hy : r < c (Nat.find hex) := Nat.find_spec hex
    have hp : 0 < Nat.find hex := by
      by_contra! h
      rw [Nat.eq_zero_of_le_zero h, c.eq_1] at hy
      omega
    let j := Nat.find hex - 1
    have hj : j + 1 = Nat.find hex := by dsimp [j]; omega
    have hlo : c j < r := by
      have h := Nat.find_min hex (show j < Nat.find hex by omega)
      exact lt_of_le_of_ne (Nat.le_of_not_gt h) (fun he => hr.2 ⟨j, he⟩)
    have hhi : r < c (j + 1) := hj ▸ hy
    have hodd : j % 2 = 1 := by
      by_contra! h
      let k := j / 2
      have he : j = 2 * k := by dsimp [k]; omega
      rw [he, c_even] at hlo
      rw [he, c_odd] at hhi
      omega
    let k := j / 2
    have hjk : j = 2 * k + 1 := by dsimp [k]; omega
    rw [hjk, c_odd] at hlo
    rw [hjk, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, c_even] at hhi
    let n := r - (2 * k + 2)
    have hnlo : c k < n + 1 := by dsimp [n]; omega
    have hnhi : n + 1 ≤ c (k + 1) := by dsimp [n]; omega
    obtain ⟨l, hllo, hlhi, hb⟩ := b_gap n
    have hkl : k = l := by
      apply le_antisymm
      · by_contra! h
        have := c_strictMono.monotone (show l + 1 ≤ k by omega)
        omega
      · by_contra! h
        have := c_strictMono.monotone (show k + 1 ≤ l by omega)
        omega
    subst l
    refine ⟨n, ?_⟩
    change b (n + 1) = r
    dsimp [n] at hb ⊢
    omega

end OMA.S_oeis_a055938

open OMA.S_oeis_a055938 in
theorem OMA.solution : type_of% @OMA.S_oeis_a055938.main := by
  classical
  let f : ℕ → ℕ := fun n => b (n + 1)
  have hmono : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro n
    change b (n + 1) < b (n + 1 + 1)
    rw [b.eq_3]
    split <;> omega
  have hf : Set.range f = S := b_range
  have hinf : S.Infinite := hf ▸ Set.infinite_range_of_injective hmono.injective
  have heq := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := fun m => m ∈ S) f
    (by
      intro x hx
      obtain ⟨i, rfl⟩ := hf.symm ▸ hx
      exact ⟨i, fun h => (hinf h).elim, rfl⟩)
    (fun i _ => b_mem i) (hmono.strictMonoOn _)
  intro n hn
  have he := heq (show n - 1 ∈ {i : ℕ | ∀ h : S.Finite, i < h.toFinset.card} from
    fun h => (hinf h).elim)
  simpa only [f, Nat.sub_add_cancel hn] using he
