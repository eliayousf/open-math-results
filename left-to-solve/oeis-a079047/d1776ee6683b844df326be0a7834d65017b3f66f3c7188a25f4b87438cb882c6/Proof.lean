import OMAStatements.S_oeis_a079047

open OMA.S_oeis_a079047 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a079047.main) := by
  intro h
  have ha : a 1 = 1 := by
    unfold a
    rw [show 1 - 1 = (0 : ℕ) by decide, Nat.nth_prime_zero_eq_two]
    decide
  have hm : 1 ∈ {m : ℕ | (∃ n, 1 ≤ n ∧ a n = m) ∧ IsSquare m} :=
    ⟨⟨1, le_rfl, ha⟩, ⟨1, rfl⟩⟩
  rw [h] at hm
  simp at hm
