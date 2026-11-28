import OMAStatements.S_oeis_a048868

/-!
Michael De Vlieger's parity conjecture for the prime reduced residues.
Source: https://oeis.org/A048868
-/

namespace A048868Proof

open OMA.S_oeis_a048868

private theorem mem_prime {n k : ℕ} :
    k ∈ (reducedResidues n).filter Nat.Prime ↔
      ((1 ≤ k ∧ k ≤ n) ∧ Nat.Coprime k n) ∧ Nat.Prime k := by
  simp [reducedResidues]

private theorem mem_nonprime {n k : ℕ} :
    k ∈ (reducedResidues n).filter (fun v => ¬ v.Prime) ↔
      ((1 ≤ k ∧ k ≤ n) ∧ Nat.Coprime k n) ∧ ¬ Nat.Prime k := by
  simp [reducedResidues]

private def partner (n k : ℕ) : ℕ :=
  if k = 2 then 1 else if k = n - 2 then n - 1 else n - k

private theorem smaller {n k : ℕ} (hk : k ∈ (reducedResidues n).filter Nat.Prime) :
    k < n := by
  rcases mem_prime.mp hk with ⟨⟨⟨_, hkn⟩, hc⟩, hp⟩
  refine lt_of_le_of_ne hkn ?_
  intro he
  subst n
  exact hp.ne_one (by simpa using hc)

private theorem no_majority {n : ℕ} (hn : 3 < n) (ho : Odd n) :
    ((reducedResidues n).filter Nat.Prime).card ≤
      ((reducedResidues n).filter (fun k => ¬ k.Prime)).card := by
  have hnodd := Nat.odd_iff.mp ho
  have hlast : ¬ Nat.Prime (n - 1) := by
    intro hp
    have he : Even (n - 1) := Nat.even_iff.mpr (by omega)
    have ht := hp.even_iff.mp he
    omega
  apply Finset.card_le_card_of_injOn (partner n)
  · intro k hk
    have hklt := smaller hk
    rcases mem_prime.mp hk with ⟨⟨⟨_, _⟩, hc⟩, hp⟩
    apply mem_nonprime.mpr
    by_cases h₂ : k = 2
    · rw [show partner n k = 1 by simp [partner, h₂]]
      exact ⟨⟨⟨le_rfl, by omega⟩, Nat.coprime_one_left n⟩, Nat.not_prime_one⟩
    · by_cases hc₂ : k = n - 2
      · rw [show partner n k = n - 1 by unfold partner; rw [if_neg h₂, if_pos hc₂]]
        have hco : Nat.Coprime (n - 1) n :=
          (Nat.coprime_self_sub_left (show 1 ≤ n by omega)).mpr (Nat.coprime_one_left n)
        exact ⟨⟨⟨by omega, by omega⟩, hco⟩, hlast⟩
      · rw [show partner n k = n - k by simp [partner, h₂, hc₂]]
        have hodd : Odd k := Nat.not_even_iff_odd.mp (fun he => h₂ (hp.even_iff.mp he))
        have hkodd := Nat.odd_iff.mp hodd
        have he : Even (n - k) := Nat.even_iff.mpr (by omega)
        have hco := (Nat.coprime_self_sub_left hklt.le).mpr hc
        refine ⟨⟨⟨by omega, by omega⟩, hco⟩, ?_⟩
        intro hprime
        have ht := hprime.even_iff.mp he
        omega
  · intro x hx y hy he
    have hxl := smaller hx
    have hyl := smaller hy
    have hxp := (mem_prime.mp hx).2
    have hyp := (mem_prime.mp hy).2
    have hx₁ := hxp.ne_one
    have hy₁ := hyp.ne_one
    have hxn : x ≠ n - 1 := fun h => hlast (h ▸ hxp)
    have hyn : y ≠ n - 1 := fun h => hlast (h ▸ hyp)
    unfold partner at he
    split_ifs at he <;> omega

theorem result : type_of% @OMA.S_oeis_a048868.main := by
  intro n hn h
  by_contra he
  have ho : Odd n := Nat.not_even_iff_odd.mp he
  by_cases hlarge : 3 < n
  · exact (not_lt_of_ge (no_majority hlarge ho)) h
  · interval_cases n <;> revert h <;> decide

end A048868Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a048868.main := A048868Proof.result
