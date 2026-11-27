import OMAStatements.S_oeis_a325525
import Mathlib.Data.Nat.Basic

/-! Consecutive gaps for OEIS A325525. Source: https://oeis.org/A325525/internal -/

namespace OMA.S_oeis_a325525

private theorem allowed (n : ℕ) (hn : 0 < n) (hp : ¬ (3 ∣ n)) (hq : ¬ (4 ∣ n)) :
    selected n := by
  rw [selected, dif_pos hn]
  exact ⟨fun h => hp h.1, fun h => hq h.1⟩

private def seed (n : ℕ) : Prop := (3 ∣ n ∧ ¬(9 ∣ n) ∧ ¬(12 ∣ n)) ∨ (4 ∣ n ∧ ¬(12 ∣ n) ∧ ¬(16 ∣ n))

private instance (n : ℕ) : Decidable (seed n) := by
  unfold seed
  infer_instance

private theorem seed_mem (n : ℕ) (hn : 0 < n) (h : seed n) : Mem n := by
  rw [seed] at h
  rcases h with ⟨hdiv, hp, hq⟩ | ⟨hdiv, hp, hq⟩
  · have heq : n = 3 * (n / 3) := by omega
    have hs : selected (n / 3) := allowed _ (by omega) (by omega) (by omega)
    refine ⟨hn, fun hsel => ?_⟩
    rw [selected, dif_pos hn] at hsel
    exact hsel.1 ⟨hdiv, hs⟩
  · have heq : n = 4 * (n / 4) := by omega
    have hs : selected (n / 4) := allowed _ (by omega) (by omega) (by omega)
    refine ⟨hn, fun hsel => ?_⟩
    rw [selected, dif_pos hn] at hsel
    exact hsel.2 ⟨hdiv, hs⟩

private theorem residue_certificate :
    ∀ r : Fin 144, ∃ d : Fin 9, seed (r.val + d.val + 1) := by
  decide +kernel

private theorem seed_add_mod (x d : ℕ) :
    seed (x % 144 + d) ↔ seed (x + d) := by
  unfold seed
  omega

private theorem gap_range (x y : ℕ) (h : Consecutive x y) : 1 ≤ y - x ∧ y - x ≤ 9 := by
  have hxy := h.1
  refine ⟨by omega, ?_⟩
  apply le_of_not_gt
  intro hgap
  obtain ⟨d, hd⟩ := residue_certificate ⟨x % 144, Nat.mod_lt _ (by decide)⟩
  have hdlt := d.isLt
  exact h.2.2.2 (x + d.val + 1) (by omega) (by omega)
    (seed_mem _ (by omega) ((seed_add_mod x (d.val + 1)).1 (by simpa [Nat.add_assoc] using hd)))

private theorem no_eight_certificate :
    ∀ r : Fin 144, ¬ (3 ∣ r.val) ∧ ¬ (4 ∣ r.val) ∨
      ¬ (3 ∣ (r.val + 8)) ∧ ¬ (4 ∣ (r.val + 8)) ∨
      ∃ d : Fin 7, seed (r.val + d.val + 1) := by
  decide +kernel

private theorem gap_ne_eight (x y : ℕ) (h : Consecutive x y) : y - x ≠ 8 := by
  intro hgap
  have hxy : y = x + 8 := by have := h.1; omega
  obtain hl | hr | ⟨d, hd⟩ := no_eight_certificate ⟨x % 144, Nat.mod_lt _ (by decide)⟩
  · change ¬ (3 ∣ (x % 144)) ∧ ¬ (4 ∣ (x % 144)) at hl
    exact h.2.1.2 (allowed x h.2.1.1 (by have := hl.1; omega) (by have := hl.2; omega))
  · change ¬ (3 ∣ (x % 144 + 8)) ∧ ¬ (4 ∣ (x % 144 + 8)) at hr
    exact h.2.2.1.2 (allowed y h.2.2.1.1 (by have := hr.1; omega) (by have := hr.2; omega))
  · exact h.2.2.2 (x + d.val + 1) (by omega) (by have := d.isLt; omega)
      (seed_mem _ (by omega) ((seed_add_mod x (d.val + 1)).1 (by simpa [Nat.add_assoc] using hd)))

theorem proved (x y : ℕ) (h : Consecutive x y) : 1 ≤ y - x ∧ y - x ≤ 9 ∧ y - x ≠ 8 := by
  exact ⟨(gap_range x y h).1, (gap_range x y h).2, gap_ne_eight x y h⟩


end OMA.S_oeis_a325525

theorem OMA.solution : type_of% @OMA.S_oeis_a325525.main :=
  OMA.S_oeis_a325525.proved
