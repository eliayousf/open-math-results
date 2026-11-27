import OMAStatements.S_oeis_a325498
import Mathlib.Data.Nat.Basic

/-! Consecutive gaps for OEIS A325498. Source: https://oeis.org/A325498/internal -/

namespace OMA.S_oeis_a325498

private theorem allowed (n : ℕ) (hn : 0 < n) (hp : ¬ (2 ∣ n)) (hq : ¬ (3 ∣ n)) :
    selected n := by
  rw [selected, dif_pos hn]
  exact ⟨fun h => hp h.1, fun h => hq h.1⟩

private def seed (n : ℕ) : Prop := ¬(2 ∣ n) ∧ ¬(3 ∣ n)

private instance (n : ℕ) : Decidable (seed n) := by
  unfold seed
  infer_instance

private theorem seed_mem (n : ℕ) (hn : 0 < n) (h : seed n) : Mem n := by
  exact allowed _ hn h.1 h.2

private theorem residue_certificate :
    ∀ r : Fin 6, ∃ d : Fin 4, seed (r.val + d.val + 1) := by
  decide +kernel

private theorem seed_add_mod (x d : ℕ) :
    seed (x % 6 + d) ↔ seed (x + d) := by
  unfold seed
  omega

private theorem gap_range (x y : ℕ) (h : Consecutive x y) : 1 ≤ y - x ∧ y - x ≤ 4 := by
  have hxy := h.1
  refine ⟨by omega, ?_⟩
  apply le_of_not_gt
  intro hgap
  obtain ⟨d, hd⟩ := residue_certificate ⟨x % 6, Nat.mod_lt _ (by decide)⟩
  have hdlt := d.isLt
  exact h.2.2.2 (x + d.val + 1) (by omega) (by omega)
    (seed_mem _ (by omega) ((seed_add_mod x (d.val + 1)).1 (by simpa [Nat.add_assoc] using hd)))

theorem proved (x y : ℕ) (h : Consecutive x y) : 1 ≤ y - x ∧ y - x ≤ 4 := by
  exact gap_range x y h


end OMA.S_oeis_a325498

theorem OMA.solution : type_of% @OMA.S_oeis_a325498.main :=
  OMA.S_oeis_a325498.proved
