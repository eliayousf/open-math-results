import OMAStatements.S_oeis_a131016

open OMA.S_oeis_a131016 in
private theorem semiprime_ge_four {n : ℕ} (h : IsSemiprime n) : 4 ≤ n := by
  obtain ⟨p, q, hp, hq, rfl⟩ := h
  exact Nat.mul_le_mul hp.two_le hq.two_le

open OMA.S_oeis_a131016 in
theorem OMA.solution : type_of% @OMA.S_oeis_a131016.main := by
  intro s hs
  have hs4 := semiprime_ge_four hs
  let d := s - 1
  have hds : d + 1 = s := by dsimp [d]; omega
  have hd : 1 < d := by omega
  have hmem : s ∈ {m : ℕ | IsSemiprime m ∧ m ≡ 1 [MOD d]} := by
    refine ⟨hs, ?_⟩
    change s % d = 1 % d
    rw [← hds, Nat.add_mod_left]
  have ha : a d ∈ {m : ℕ | IsSemiprime m ∧ m ≡ 1 [MOD d]} :=
    Nat.sInf_mem ⟨s, hmem⟩
  refine ⟨d, by omega, le_antisymm (Nat.sInf_le hmem) ?_⟩
  by_contra! h
  have hle : a d ≤ d := by omega
  have hmod : a d % d = 1 % d := ha.2
  rw [Nat.mod_eq_of_lt hd] at hmod
  rcases lt_or_eq_of_le hle with hlt | heq
  · rw [Nat.mod_eq_of_lt hlt] at hmod
    have hfour := semiprime_ge_four ha.1
    omega
  · rw [heq, Nat.mod_self] at hmod
    omega
