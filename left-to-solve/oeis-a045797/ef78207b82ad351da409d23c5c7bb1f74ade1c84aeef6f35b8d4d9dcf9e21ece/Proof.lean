import OMAStatements.S_oeis_a045797

/-!
Colin Barker proposed the recurrence in OEIS A045797 in 2012, and
Jianing Song confirmed it in 2019.
Source: https://oeis.org/A045797
-/

namespace A045797Proof

open OMA.S_oeis_a045797

private theorem residue_table :
    ∀ r : Fin 20, (Nat.gcd r.val 10 = 1 ∧ r.val < 10) ↔
      r.val = 1 ∨ r.val = 3 ∨ r.val = 7 ∨ r.val = 9 := by decide

private theorem evenish_iff (k : ℕ) :
    evenish k ↔ k % 20 = 1 ∨ k % 20 = 3 ∨ k % 20 = 7 ∨ k % 20 = 9 := by
  have hg : Nat.gcd k 10 = Nat.gcd (k % 20) 10 := by
    rw [Nat.gcd_comm k 10, Nat.gcd_rec 10 k, Nat.gcd_comm (k % 20) 10,
      Nat.gcd_rec 10 (k % 20), Nat.mod_mod_of_dvd k (by decide : 10 ∣ 20)]
  have ht : (k / 10 % 10) % 2 = 0 ↔ k % 20 < 10 := by omega
  change (Nat.gcd k 10 = 1 ∧ (k / 10 % 10) % 2 = 0) ↔ _
  rw [hg, ht]
  exact residue_table ⟨k % 20, Nat.mod_lt _ (by decide)⟩

private def offset (r : ℕ) : ℕ :=
  if r = 0 then 1 else if r = 1 then 3 else if r = 2 then 7 else 9

private def listing (i : ℕ) : ℕ := 20 * (i / 4) + offset (i % 4)

private theorem listing_mono : StrictMono listing := by
  intro i j hij
  change listing i < listing j
  unfold listing offset
  split_ifs <;> omega

private theorem listing_mem (i : ℕ) : evenish (listing i) := by
  rw [evenish_iff]
  unfold listing offset
  split_ifs <;> omega

private theorem listing_at (q i : ℕ) (hi : i < 4) :
    listing (4*q + i) = 20*q + offset i := by
  have hdiv : (4*q + i) / 4 = q := by omega
  have hmod : (4*q + i) % 4 = i := by omega
  rw [listing, hdiv, hmod]

private theorem listing_surj {k : ℕ} (hk : evenish k) : ∃ i : ℕ, listing i = k := by
  rcases (evenish_iff k).1 hk with h | h | h | h
  · refine ⟨4*(k/20)+0, ?_⟩
    rw [listing_at _ _ (by decide)]
    simp [offset]
    omega
  · refine ⟨4*(k/20)+1, ?_⟩
    rw [listing_at _ _ (by decide)]
    simp [offset]
    omega
  · refine ⟨4*(k/20)+2, ?_⟩
    rw [listing_at _ _ (by decide)]
    simp [offset]
    omega
  · refine ⟨4*(k/20)+3, ?_⟩
    rw [listing_at _ _ (by decide)]
    simp [offset]
    omega

private theorem listing_eq_nth (i : ℕ) : listing i = Nat.nth evenish i := by
  have hsub : Set.range listing ⊆ Set.ofPred evenish := by
    rintro k ⟨j, rfl⟩
    exact listing_mem j
  have hinf : (Set.ofPred evenish).Infinite :=
    (Set.infinite_range_of_injective listing_mono.injective).mono hsub
  have hdom (j : ℕ) : ∀ hf : (Set.ofPred evenish).Finite, j < hf.toFinset.card :=
    fun hf => (hinf hf).elim
  exact Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := evenish) listing
    (fun k hk => by
      obtain ⟨j, hj⟩ := listing_surj hk
      exact ⟨j, hdom j, hj⟩)
    (fun j _ => show evenish (listing j) from listing_mem j)
    (listing_mono.strictMonoOn _) (hdom i)

private theorem period (n : ℕ) (hn : 1 ≤ n) : a (n+4) = a n + 20 := by
  rw [a, a, ← listing_eq_nth, ← listing_eq_nth]
  have hshift : n + 4 - 1 = (n - 1) + 4 := by omega
  have hm : ((n - 1) + 4) % 4 = (n - 1) % 4 := by omega
  rw [hshift, listing, listing, hm]
  omega

end A045797Proof

open OMA.S_oeis_a045797

theorem OMA.solution : type_of% @OMA.S_oeis_a045797.main := by
  intro n hn
  have h := A045797Proof.period (n - 4) (by omega)
  have h' := A045797Proof.period (n - 5) (by omega)
  rw [show n - 4 + 4 = n by omega] at h
  rw [show n - 5 + 4 = n - 1 by omega] at h'
  omega
