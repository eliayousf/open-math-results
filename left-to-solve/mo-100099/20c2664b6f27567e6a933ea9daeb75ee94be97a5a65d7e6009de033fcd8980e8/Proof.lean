import OMAStatements.S_mo_100099
import Mathlib

open OMA.S_mo_100099

private theorem paper_of_adj {a p t : ℕ} {paper : ℕ → Fin p → Sym2 (Mathematician a)}
    {u v : Mathematician a} (h : (collab paper t).Adj u v) :
    u ≠ v ∧ ∃ y, y ≤ t ∧ ∃ j, paper y j = s(u, v) := by
  rw [collab, SimpleGraph.fromRel_adj] at h
  rcases h with ⟨huv, h | h⟩
  · exact ⟨huv, h⟩
  · obtain ⟨y, hy, j, hj⟩ := h
    exact ⟨huv, y, hy, j, hj.trans Sym2.eq_swap⟩

private theorem adj_of_paper {a p t : ℕ} {paper : ℕ → Fin p → Sym2 (Mathematician a)}
    {u v : Mathematician a} (huv : u ≠ v) {y : ℕ} (hy : y ≤ t)
    {j : Fin p} (hj : paper y j = s(u, v)) : (collab paper t).Adj u v := by
  rw [collab, SimpleGraph.fromRel_adj]
  exact ⟨huv, Or.inl ⟨y, hy, j, hj⟩⟩

private theorem collab_mono {a p : ℕ} (paper : ℕ → Fin p → Sym2 (Mathematician a))
    {T t : ℕ} (ht : T ≤ t) : collab paper T ≤ collab paper t := by
  intro u v h
  obtain ⟨huv, y, hy, j, hj⟩ := paper_of_adj h
  exact adj_of_paper huv (hy.trans ht) hj

private theorem cutoff_walk {a p L t T : ℕ} {paper : ℕ → Fin p → Sym2 (Mathematician a)}
    (hadm : Admissible L paper) {u v : Mathematician a}
    (w : (collab paper t).Walk u v) :
    u.1 + w.length * L ≤ T → ∃ w' : (collab paper T).Walk u v, w'.length = w.length ∧ v.1 ≤ T := by
  induction w with
  | nil =>
    intro h
    exact ⟨SimpleGraph.Walk.nil, rfl, by simpa using h⟩
  | @cons u x v h w ih =>
    intro hbound
    simp only [SimpleGraph.Walk.length_cons, Nat.add_mul, one_mul] at hbound
    obtain ⟨hux, y, _, j, hj⟩ := paper_of_adj h
    have hu := (hadm y j).2 u (hj ▸ Sym2.mem_mk_left u x)
    have hx := (hadm y j).2 x (hj ▸ Sym2.mem_mk_right u x)
    change u.1 ≤ y ∧ y < u.1 + L at hu
    change x.1 ≤ y ∧ y < x.1 + L at hx
    obtain ⟨w', hlen, hv⟩ := ih (by omega)
    exact ⟨SimpleGraph.Walk.cons (adj_of_paper hux (by omega) hj) w', by simp [hlen], hv⟩

theorem OMA.solution : type_of% @OMA.S_mo_100099.main := by
  intro a p L erdos paper hadm n _
  let T := erdos.1 + n * L
  let S : Set (Mathematician a) := {v | (collab paper T).edist erdos v = (n : ℕ∞)}
  have hfinite : S.Finite := by
    apply ((Set.finite_Iic T).prod (Set.finite_univ : (Set.univ : Set (Fin a)).Finite)).subset
    intro v hv
    obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hv
    obtain ⟨_, _, hb⟩ := cutoff_walk (T := T) hadm w (by simp [T, hw])
    exact ⟨hb, Set.mem_univ _⟩
  obtain ⟨c, hc⟩ := hfinite.exists_encard_eq_coe
  refine ⟨T, c, ?_⟩
  intro t ht
  suffices hs : {v | (collab paper t).edist erdos v = (n : ℕ∞)} = S by
    rw [E, hs, hc]
  ext v
  change ((collab paper t).edist erdos v = (n : ℕ∞)) ↔
    ((collab paper T).edist erdos v = (n : ℕ∞))
  have hmono : (collab paper t).edist erdos v ≤ (collab paper T).edist erdos v :=
    SimpleGraph.edist_anti (collab_mono paper ht.le)
  constructor
  · intro h
    obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_eq_coe h
    obtain ⟨w', hlen, _⟩ := cutoff_walk (T := T) hadm w (by simp [T, hw])
    have hdist := w'.edist_le
    rw [hlen, hw] at hdist
    rw [h] at hmono
    exact le_antisymm hdist hmono
  · intro h
    have ht_le : (collab paper t).edist erdos v ≤ (n : ℕ∞) := hmono.trans_eq h
    have hne : (collab paper t).edist erdos v ≠ ⊤ := by
      intro heq
      simp [heq] at ht_le
    obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
    have hlen : w.length ≤ n := ENat.natCast_le_natCast.mp (hw.le.trans ht_le)
    have hb : erdos.1 + w.length * L ≤ T :=
      Nat.add_le_add_left (Nat.mul_le_mul_right L hlen) erdos.1
    obtain ⟨w', hw', _⟩ := cutoff_walk hadm w hb
    have hdist := w'.edist_le
    rw [hw', hw, h] at hdist
    exact le_antisymm ht_le hdist
