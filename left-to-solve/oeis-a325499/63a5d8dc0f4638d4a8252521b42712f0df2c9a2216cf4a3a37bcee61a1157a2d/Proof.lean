import OMAStatements.S_oeis_a325499
import Mathlib.Data.Nat.Basic

/-! Consecutive gaps for OEIS A325499. Source: https://oeis.org/A325499/internal -/

namespace OMA.S_oeis_a325499

private theorem allowed (n : ℕ) (hn : 0 < n) (hp : ¬ (2 ∣ n)) (hq : ¬ (3 ∣ n)) :
    selected n := by
  rw [selected, dif_pos hn]
  exact ⟨fun h => hp h.1, fun h => hq h.1⟩

private def seed (n : ℕ) : Prop := (2 ∣ n ∧ ¬(4 ∣ n) ∧ ¬(6 ∣ n)) ∨ (3 ∣ n ∧ ¬(6 ∣ n) ∧ ¬(9 ∣ n))

private instance (n : ℕ) : Decidable (seed n) := by
  unfold seed
  infer_instance

private theorem seed_mem (n : ℕ) (hn : 0 < n) (h : seed n) : Mem n := by
  rw [seed] at h
  rcases h with ⟨hdiv, hp, hq⟩ | ⟨hdiv, hp, hq⟩
  · have heq : n = 2 * (n / 2) := by omega
    have hs : selected (n / 2) := allowed _ (by omega) (by omega) (by omega)
    refine ⟨hn, fun hsel => ?_⟩
    rw [selected, dif_pos hn] at hsel
    exact hsel.1 ⟨hdiv, hs⟩
  · have heq : n = 3 * (n / 3) := by omega
    have hs : selected (n / 3) := allowed _ (by omega) (by omega) (by omega)
    refine ⟨hn, fun hsel => ?_⟩
    rw [selected, dif_pos hn] at hsel
    exact hsel.2 ⟨hdiv, hs⟩

private theorem residue_certificate :
    ∀ r : Fin 36, ∃ d : Fin 7, seed (r.val + d.val + 1) := by
  decide +kernel

private theorem seed_add_mod (x d : ℕ) :
    seed (x % 36 + d) ↔ seed (x + d) := by
  unfold seed
  omega

private theorem gap_range (x y : ℕ) (h : Consecutive x y) : 1 ≤ y - x ∧ y - x ≤ 7 := by
  have hxy := h.1
  refine ⟨by omega, ?_⟩
  apply le_of_not_gt
  intro hgap
  obtain ⟨d, hd⟩ := residue_certificate ⟨x % 36, Nat.mod_lt _ (by decide)⟩
  have hdlt := d.isLt
  exact h.2.2.2 (x + d.val + 1) (by omega) (by omega)
    (seed_mem _ (by omega) ((seed_add_mod x (d.val + 1)).1 (by simpa [Nat.add_assoc] using hd)))

theorem proved (x y : ℕ) (h : Consecutive x y) : 1 ≤ y - x ∧ y - x ≤ 7 := by
  exact gap_range x y h


end OMA.S_oeis_a325499

theorem OMA.solution : type_of% @OMA.S_oeis_a325499.main :=
  OMA.S_oeis_a325499.proved
