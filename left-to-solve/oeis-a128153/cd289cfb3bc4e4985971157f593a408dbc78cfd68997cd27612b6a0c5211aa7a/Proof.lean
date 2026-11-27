import OMAStatements.S_oeis_a128153

namespace A128153Proof

open OMA.S_oeis_a128153

def first (m k : ℕ) (hk : k ≤ m) : Offset m :=
  .inl ⟨k, by omega⟩

def rotate {α : Type} (p : Fin 5 → α) (r : Fin 5) (i : Fin 5) : α :=
  p (i + r)

def oneBase (m : ℕ) (t : Fin m) : Fin 5 → Offset m :=
  ![first m m le_rfl, first m (m - (t.val + 1)) (by omega),
    first m (m - (t.val + 1)) (by omega), first m m le_rfl, .inr t]

def twoBase (m : ℕ) (u v : Fin m) : Fin 5 → Offset m :=
  ![first m (m - (u.val + 1)) (by omega),
    first m (m - (u.val + v.val + 2)) (by omega),
    first m (m - (v.val + 1)) (by omega), .inr u, .inr v]

def Balanced (m : ℕ) (p : Fin 5 → Offset m) : Prop :=
  ∀ i, residual m p i = residual m p 0

inductive Shape (m : ℕ) (p : Fin 5 → Offset m) : Prop
  | allA (t : Fin (m + 1)) (hp : p = fun _ => .inl t)
  | allB (t : Fin m) (hp : p = fun _ => .inr t)
  | oneB (r : Fin 5) (t : Fin m) (hp : p = rotate (oneBase m t) r)
  | twoB (r : Fin 5) (u v : Fin m) (ht : u.val + v.val + 2 ≤ m)
      (hp : p = rotate (twoBase m u v) r)

private theorem vectorExt {α : Type} {p q : Fin 5 → α}
    (h0 : p 0 = q 0) (h1 : p 1 = q 1) (h2 : p 2 = q 2)
    (h3 : p 3 = q 3) (h4 : p 4 = q 4) : p = q := by
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

set_option maxHeartbeats 2500000 in
theorem classify (m : ℕ) (p : Fin 5 → Offset m) (hb : Balanced m p) : Shape m p := by
  let a0 := coefficients m (p 0)
  let a1 := coefficients m (p 1)
  let a2 := coefficients m (p 2)
  let a3 := coefficients m (p 3)
  let a4 := coefficients m (p 4)
  have b1 : (a0.1 + a2.1 + a1.1 - a1.2,
      a0.2 + a2.2 - a1.1) = (a4.1 + a1.1 + a0.1 - a0.2,
      a4.2 + a1.2 - a0.1) := hb 1
  have b2 : (a1.1 + a3.1 + a2.1 - a2.2,
      a1.2 + a3.2 - a2.1) = (a4.1 + a1.1 + a0.1 - a0.2,
      a4.2 + a1.2 - a0.1) := hb 2
  have b3 : (a2.1 + a4.1 + a3.1 - a3.2,
      a2.2 + a4.2 - a3.1) = (a4.1 + a1.1 + a0.1 - a0.2,
      a4.2 + a1.2 - a0.1) := hb 3
  have b4 : (a3.1 + a0.1 + a4.1 - a4.2,
      a3.2 + a0.2 - a4.1) = (a4.1 + a1.1 + a0.1 - a0.2,
      a4.2 + a1.2 - a0.1) := hb 4
  cases e0 : p 0 <;> rename_i x0
  all_goals cases e1 : p 1 <;> rename_i x1
  all_goals cases e2 : p 2 <;> rename_i x2
  all_goals cases e3 : p 3 <;> rename_i x3
  all_goals cases e4 : p 4 <;> rename_i x4
  all_goals have hx0 := x0.isLt
  all_goals have hx1 := x1.isLt
  all_goals have hx2 := x2.isLt
  all_goals have hx3 := x3.isLt
  all_goals have hx4 := x4.isLt
  all_goals simp only [a0, a1, a2, a3, a4, e0, e1, e2, e3, e4, coefficients, Prod.mk.injEq] at b1 b2 b3 b4
  · -- AAAAA
    apply Shape.allA x0
    apply vectorExt
    all_goals first | rw [e0] | rw [e1] | rw [e2] | rw [e3] | rw [e4]
    all_goals apply congrArg Sum.inl
    all_goals apply Fin.ext
    all_goals omega
  · -- AAAAB
    apply Shape.oneB 0 x4
    apply vectorExt
    all_goals first | rw [e0] | rw [e1] | rw [e2] | rw [e3] | rw [e4]
    all_goals try rfl
    all_goals apply congrArg Sum.inl
    all_goals apply Fin.ext
    all_goals dsimp [rotate, oneBase, first]
    all_goals omega
  · -- AAABA
    apply Shape.oneB 1 x3
    apply vectorExt
    all_goals first | rw [e0] | rw [e1] | rw [e2] | rw [e3] | rw [e4]
    all_goals try rfl
    all_goals apply congrArg Sum.inl
    all_goals apply Fin.ext
    all_goals dsimp [rotate, oneBase, first]
    all_goals omega
  · -- AAABB
    refine Shape.twoB 0 x3 x4 (by omega) ?_
    apply vectorExt
    all_goals first | rw [e0] | rw [e1] | rw [e2] | rw [e3] | rw [e4]
    all_goals try rfl
    all_goals apply congrArg Sum.inl
    all_goals apply Fin.ext
    all_goals dsimp [rotate, twoBase, first]
    all_goals omega
  · -- AABAA
    apply Shape.oneB 2 x2
    apply vectorExt
    all_goals first | rw [e0] | rw [e1] | rw [e2] | rw [e3] | rw [e4]
    all_goals try rfl
    all_goals apply congrArg Sum.inl
    all_goals apply Fin.ext
    all_goals dsimp [rotate, oneBase, first]
    all_goals omega
  · -- AABAB
    omega
  · -- AABBA
    refine Shape.twoB 1 x2 x3 (by omega) ?_
    apply vectorExt
    all_goals first | rw [e0] | rw [e1] | rw [e2] | rw [e3] | rw [e4]
    all_goals try rfl
    all_goals apply congrArg Sum.inl
    all_goals apply Fin.ext
    all_goals dsimp [rotate, twoBase, first]
    all_goals omega
  · -- AABBB
    omega
  · -- ABAAA
    apply Shape.oneB 3 x1
    apply vectorExt
    all_goals first | rw [e0] | rw [e1] | rw [e2] | rw [e3] | rw [e4]
    all_goals try rfl
    all_goals apply congrArg Sum.inl
    all_goals apply Fin.ext
    all_goals dsimp [rotate, oneBase, first]
    all_goals omega
  · -- ABAAB
    omega
  · -- ABABA
    omega
  · -- ABABB
    omega
  · -- ABBAA
    refine Shape.twoB 2 x1 x2 (by omega) ?_
    apply vectorExt
    all_goals first | rw [e0] | rw [e1] | rw [e2] | rw [e3] | rw [e4]
    all_goals try rfl
    all_goals apply congrArg Sum.inl
    all_goals apply Fin.ext
    all_goals dsimp [rotate, twoBase, first]
    all_goals omega
  · -- ABBAB
    omega
  · -- ABBBA
    omega
  · -- ABBBB
    omega
  · -- BAAAA
    apply Shape.oneB 4 x0
    apply vectorExt
    all_goals first | rw [e0] | rw [e1] | rw [e2] | rw [e3] | rw [e4]
    all_goals try rfl
    all_goals apply congrArg Sum.inl
    all_goals apply Fin.ext
    all_goals dsimp [rotate, oneBase, first]
    all_goals omega
  · -- BAAAB
    refine Shape.twoB 4 x4 x0 (by omega) ?_
    apply vectorExt
    all_goals first | rw [e0] | rw [e1] | rw [e2] | rw [e3] | rw [e4]
    all_goals try rfl
    all_goals apply congrArg Sum.inl
    all_goals apply Fin.ext
    all_goals dsimp [rotate, twoBase, first]
    all_goals omega
  · -- BAABA
    omega
  · -- BAABB
    omega
  · -- BABAA
    omega
  · -- BABAB
    omega
  · -- BABBA
    omega
  · -- BABBB
    omega
  · -- BBAAA
    refine Shape.twoB 3 x0 x1 (by omega) ?_
    apply vectorExt
    all_goals first | rw [e0] | rw [e1] | rw [e2] | rw [e3] | rw [e4]
    all_goals try rfl
    all_goals apply congrArg Sum.inl
    all_goals apply Fin.ext
    all_goals dsimp [rotate, twoBase, first]
    all_goals omega
  · -- BBAAB
    omega
  · -- BBABA
    omega
  · -- BBABB
    omega
  · -- BBBAA
    omega
  · -- BBBAB
    omega
  · -- BBBBA
    omega
  · -- BBBBB
    apply Shape.allB x0
    apply vectorExt
    all_goals first | rw [e0] | rw [e1] | rw [e2] | rw [e3] | rw [e4]
    all_goals apply congrArg Sum.inr
    all_goals apply Fin.ext
    all_goals omega

end A128153Proof

namespace A128153Proof

open OMA.S_oeis_a128153

private theorem phi_sq : phi ^ 2 = phi + 1 := Real.goldenRatio_sq
private theorem phi_bounds : 4 / 3 < phi ∧ phi < 7 / 4 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h' := Real.sqrt_nonneg 5
  unfold phi
  constructor <;> nlinarith

noncomputable def av (m t : ℝ) : ℝ := m + (phi - 3) * t
noncomputable def bv (m t : ℝ) : ℝ := (phi - 2) * m + (4 - 3 * phi) * t

theorem value_A {m k : ℕ} (hk : k ≤ m) :
    value m (first m k hk) = av m k := by
  unfold first value coefficients av
  push_cast
  ring

theorem value_B {m : ℕ} (t : Fin m) :
    value m (.inr t) = bv m ((t.val : ℝ) + 1) := by
  unfold value coefficients bv
  push_cast
  ring

theorem av_antitone {m x y : ℝ} (h : x ≤ y) : av m y ≤ av m x := by
  unfold av
  have hcoef : phi - 3 ≤ 0 := by linarith [phi_bounds.2]
  simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonpos_left h hcoef) m

theorem bv_base_lt {m t : ℝ} (h : 0 < t) : bv m t < av m m := by
  unfold bv av
  have hh : (4 - 3 * phi) * t < 0 := mul_neg_of_neg_of_pos (by linarith [phi_bounds.1]) h
  linarith

private theorem av_ne_zero {m t : ℕ} (hm : 0 < m) : av m t ≠ 0 := by
  intro h
  by_cases hz : t = 0
  · simp [hz, av, Nat.ne_of_gt hm] at h
  have hq : phi ≠ ((3 * (t : ℚ) - m) / t : ℚ) := Real.goldenRatio_irrational.ne_rat _
  apply hq
  push_cast
  apply (eq_div_iff (by exact_mod_cast hz : (t : ℝ) ≠ 0)).2
  unfold av at h
  linarith

private theorem av_low_bound (m : ℝ) :
    -(2 * phi - 2) * av m m = (4 * phi - 6) * m := by
  unfold av
  ring_nf
  rw [phi_sq]
  ring

private theorem bv_neg {m t : ℝ} (hm : 0 < m) (ht : 0 < t) : bv m t < 0 := by
  exact add_neg (mul_neg_of_neg_of_pos (by linarith [phi_bounds.2]) hm)
    (mul_neg_of_neg_of_pos (by linarith [phi_bounds.1]) ht)

private theorem bv_full_bound (m t : ℝ) :
    bv m t - (2 * phi - 1) * bv m t - m = (7 - 4 * phi) * (2*t - m) := by
  unfold bv
  ring_nf
  rw [phi_sq]
  ring

theorem valid_A {m : ℕ} (hm : 0 < m) (t : Fin (m+1)) :
    Valid m (fun _ => .inl t) := by
  have ht : t.val ≤ m := by omega
  have he : apothem m (fun _ => .inl t) = av m t.val := by simp [apothem, ← value_A ht, first]
  constructor
  · intro i
    rfl
  · rw [he]
    rcases lt_or_gt_of_ne (av_ne_zero (t := t.val) hm) with h | h
    · right
      refine ⟨h, fun _ => ?_⟩
      have hb := av_antitone (m := (m : ℝ)) (show (t.val : ℝ) ≤ m by exact_mod_cast ht)
      have hh : -(2 * phi - 2) * av m t.val ≤ -(2 * phi - 2) * av m m :=
        mul_le_mul_of_nonpos_left hb (by linarith [phi_bounds.1])
      rw [av_low_bound] at hh
      have hj : (4 * phi - 6) * m ≤ (m : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right (show 4 * phi - 6 ≤ 1 by linarith [phi_bounds.2])
          (show 0 ≤ (m : ℝ) by positivity)
      rw [show value m (.inl t) = av m t.val from value_A ht]
      linarith
    · exact Or.inl h

theorem valid_B {m : ℕ} (hm : 0 < m) (t : Fin m) :
    Valid m (fun _ => .inr t) ↔ 2 * (t.val + 1) ≤ m := by
  have he : apothem m (fun _ => .inr t) = bv m ((t.val : ℝ) + 1) := by simp [apothem, value_B]
  have ht : 0 < (t.val : ℝ) + 1 := by positivity
  have hneg := bv_neg (show 0 < (m : ℝ) by exact_mod_cast hm) ht
  have hp : 0 < 7 - 4 * phi := by linarith [phi_bounds.2]
  constructor
  · intro ⟨_, hpent⟩
    rw [he] at hpent
    rcases hpent with h | ⟨_, h⟩
    · linarith
    have hi := h (0 : Fin 5)
    rw [value_B] at hi
    have hd := bv_full_bound (m : ℝ) ((t.val : ℝ) + 1)
    have hh : (7 - 4 * phi) * (2 * ((t.val : ℝ) + 1) - m) ≤ 0 := by linarith
    have hj : 2 * ((t.val : ℝ) + 1) - m ≤ 0 := nonpos_of_mul_nonpos_right hh hp
    exact_mod_cast (sub_nonpos.mp hj)
  · intro hh
    constructor
    · intro i
      rfl
    · rw [he]
      right
      refine ⟨hneg, fun _ => ?_⟩
      rw [value_B]
      have h' : 2 * ((t.val : ℝ) + 1) ≤ m := by exact_mod_cast hh
      have hd := bv_full_bound (m : ℝ) ((t.val : ℝ) + 1)
      have hj := mul_nonpos_of_nonneg_of_nonpos hp.le (sub_nonpos.mpr h')
      linarith

theorem mixed_bound {m t y : ℝ} (ht : t ≤ m) (hy : y ≤ av m (m-t)) :
    y - (2 * phi - 1) * ((phi - 2) * (m-t)) ≤ m := by
  have h : av m (m-t) - (2 * phi - 1) * ((phi - 2) * (m-t)) - m =
      (7 - 4*phi) * (t-m) := by
    unfold av
    ring_nf
    rw [phi_sq]
    ring
  have h' := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 7 - 4*phi by linarith [phi_bounds.2])
    (sub_nonpos.mpr ht)
  linarith

end A128153Proof

namespace A128153Proof

open OMA.S_oeis_a128153

private theorem residual_rot {m : ℕ} (p : Fin 5 → Offset m) (r i : Fin 5) :
    OMA.S_oeis_a128153.residual m (rotate p r) i =
      OMA.S_oeis_a128153.residual m p (i+r) := by
  have h4 : shift i 4 + r = shift (i+r) 4 := by
    change i + 4 + r = i + r + 4
    ac_rfl
  have h1 : shift i 1 + r = shift (i+r) 1 := by
    change i + 1 + r = i + r + 1
    ac_rfl
  simp [OMA.S_oeis_a128153.residual, rotate, h4, h1]

private theorem apothem_rot {m : ℕ} (p : Fin 5 → Offset m) (r : Fin 5) :
    apothem m (rotate p r) = apothem m p := by
  unfold apothem rotate
  exact congrArg (fun x : ℝ => x / 5)
    ((Equiv.addRight r).bijective.sum_comp (fun i => value m (p i)))

theorem rotate_valid {m : ℕ} (p : Fin 5 → Offset m) (r : Fin 5) :
    Valid m (rotate p r) ↔ Valid m p := by
  have hs : Function.Surjective (fun i : Fin 5 => i+r) := (Equiv.addRight r).surjective
  unfold Valid
  simp only [residual_rot, apothem_rot, rotate, zero_add]
  constructor
  · rintro ⟨h, h'⟩
    constructor
    · intro i
      obtain ⟨j,hj⟩ := hs i
      obtain ⟨k,hk⟩ := hs 0
      change j+r = i at hj
      change k+r = 0 at hk
      calc
        OMA.S_oeis_a128153.residual m p i =
          OMA.S_oeis_a128153.residual m p r := by simpa only [hj] using h j
        _ = OMA.S_oeis_a128153.residual m p 0 := by simpa only [hk] using (h k).symm
    · rcases h' with h' | ⟨h', hz⟩
      · exact Or.inl h'
      refine Or.inr ⟨h', fun i => ?_⟩
      obtain ⟨j,hj⟩ := hs i
      change j+r = i at hj
      simpa only [hj] using hz j
  · rintro ⟨h, h'⟩
    refine ⟨fun i => (h (i+r)).trans (h r).symm, ?_⟩
    rcases h' with h' | ⟨h', hz⟩
    · exact Or.inl h'
    exact Or.inr ⟨h', fun i => hz (i+r)⟩

private theorem one_balanced {m : ℕ} (t : Fin m) : Balanced m (oneBase m t) := by
  have ht := t.isLt
  intro i
  fin_cases i <;>
    simp [OMA.S_oeis_a128153.residual, shift, oneBase, first, coefficients] <;> omega

private theorem two_balanced {m : ℕ} (u v : Fin m) (h : u.val+v.val+2 ≤ m) :
    Balanced m (twoBase m u v) := by
  have hu := u.isLt
  have hv := v.isLt
  intro i
  fin_cases i <;>
    simp [OMA.S_oeis_a128153.residual, shift, twoBase, first, coefficients] <;> omega

private theorem one_apothem {m : ℕ} (t : Fin m) :
    apothem m (oneBase m t) = (phi - 2) * ((m : ℝ) - (t.val+1)) := by
  have ht : t.val+1 ≤ m := t.isLt
  unfold apothem oneBase
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    add_zero, value_A, value_B]
  rw [Nat.cast_sub ht]
  push_cast
  unfold av bv
  ring

private theorem two_apothem {m : ℕ} (u v : Fin m) (h : u.val+v.val+2 ≤ m) :
    apothem m (twoBase m u v) = (phi - 2) * ((m : ℝ) - (u.val+v.val+2)) := by
  have hu : u.val+1 ≤ m := by omega
  have hv : v.val+1 ≤ m := by omega
  unfold apothem twoBase
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    add_zero, value_A, value_B]
  rw [Nat.cast_sub hu, Nat.cast_sub hv, Nat.cast_sub h]
  push_cast
  unfold av bv
  ring

theorem valid_one {m : ℕ} (t : Fin m) : Valid m (oneBase m t) ↔ t.val+1 < m := by
  have ht : t.val+1 ≤ m := t.isLt
  have hr : 0 < (t.val : ℝ)+1 := by positivity
  have hphi : phi - 2 < 0 := by
    have h : phi < 2 := Real.goldenRatio_lt_two
    linarith
  constructor
  · intro ⟨_, h⟩
    by_contra! hn
    have heq : (m : ℝ) = t.val+1 := by exact_mod_cast (show m = t.val+1 by omega)
    rw [one_apothem, heq, sub_self, mul_zero] at h
    norm_num at h
  · intro hh
    refine ⟨one_balanced t, Or.inr ⟨?_, fun i => ?_⟩⟩
    · rw [one_apothem]
      exact mul_neg_of_neg_of_pos hphi (sub_pos.mpr (by exact_mod_cast hh))
    · rw [one_apothem]
      apply mixed_bound (show (t.val : ℝ) + 1 ≤ m by exact_mod_cast ht)
      fin_cases i
      · change value m (first m m le_rfl) ≤ _
        rw [value_A]
        exact av_antitone (by linarith)
      · change value m (first m (m-(t.val+1)) (by omega)) ≤ _
        rw [value_A, Nat.cast_sub ht]
        push_cast
        rfl
      · change value m (first m (m-(t.val+1)) (by omega)) ≤ _
        rw [value_A, Nat.cast_sub ht]
        push_cast
        rfl
      · change value m (first m m le_rfl) ≤ _
        rw [value_A]
        exact av_antitone (by linarith)
      · change value m (.inr t) ≤ _
        rw [value_B]
        exact (bv_base_lt (m := m) hr).le.trans (av_antitone (by linarith))

theorem valid_two {m : ℕ} (u v : Fin m) (h : u.val+v.val+2 ≤ m) :
    Valid m (twoBase m u v) ↔ u.val+v.val+2 < m := by
  have hu : u.val+1 ≤ m := by omega
  have hv : v.val+1 ≤ m := by omega
  have hur : 0 < (u.val : ℝ)+1 := by positivity
  have hvr : 0 < (v.val : ℝ)+1 := by positivity
  have hphi : phi - 2 < 0 := by
    have h : phi < 2 := Real.goldenRatio_lt_two
    linarith
  constructor
  · intro ⟨_, hp⟩
    by_contra! hn
    have heq : (m : ℝ) = u.val+v.val+2 := by
      exact_mod_cast (show m = u.val+v.val+2 by omega)
    rw [two_apothem u v h, heq, sub_self, mul_zero] at hp
    norm_num at hp
  · intro hh
    refine ⟨two_balanced u v h, Or.inr ⟨?_, fun i => ?_⟩⟩
    · rw [two_apothem u v h]
      exact mul_neg_of_neg_of_pos hphi (sub_pos.mpr (by exact_mod_cast hh))
    · rw [two_apothem u v h]
      apply mixed_bound (show (u.val : ℝ) + v.val + 2 ≤ m by exact_mod_cast h)
      fin_cases i
      · change value m (first m (m-(u.val+1)) (by omega)) ≤ _
        rw [value_A, Nat.cast_sub hu]
        push_cast
        exact av_antitone (by linarith)
      · change value m (first m (m-(u.val+v.val+2)) (by omega)) ≤ _
        rw [value_A, Nat.cast_sub h]
        push_cast
        rfl
      · change value m (first m (m-(v.val+1)) (by omega)) ≤ _
        rw [value_A, Nat.cast_sub hv]
        push_cast
        exact av_antitone (by linarith)
      · change value m (.inr u) ≤ _
        rw [value_B]
        exact (bv_base_lt (m := m) hur).le.trans (av_antitone (by linarith))
      · change value m (.inr v) ≤ _
        rw [value_B]
        exact (bv_base_lt (m := m) hvr).le.trans (av_antitone (by linarith))

end A128153Proof

namespace A128153Proof

open OMA.S_oeis_a128153

abbrev Choices (m : ℕ) :=
  Fin (m+1) ⊕ (Fin (m/2) ⊕ ((Fin 5 × Fin (m-1)) ⊕
    (Fin 5 × (Σ t : Fin (m-1), Fin t.val))))

private def asB {m k : ℕ} (t : Fin k) (h : k ≤ m) : Fin m := ⟨t.val, lt_of_lt_of_le t.isLt h⟩

private def uParam {m : ℕ} (t : Fin (m-1)) (u : Fin t.val) : Fin m := ⟨u.val, by omega⟩

private def vParam {m : ℕ} (t : Fin (m-1)) (u : Fin t.val) : Fin m :=
  ⟨t.val-u.val-1, by omega⟩

private def render (m : ℕ) : Choices m → Fin 5 → Offset m
  | .inl t => fun _ => .inl t
  | .inr (.inl t) => fun _ => .inr (asB t (by omega))
  | .inr (.inr (.inl (r,t))) => rotate (oneBase m (asB t (by omega))) r
  | .inr (.inr (.inr (r,⟨t,u⟩))) => rotate (twoBase m (uParam t u) (vParam t u)) r

private theorem render_valid {m : ℕ} (hm : 0 < m) (q : Choices m) : Valid m (render m q) := by
  rcases q with t | t | ⟨r,t⟩ | ⟨r,⟨t,u⟩⟩
  · exact valid_A hm t
  · apply (valid_B hm _).2
    have ht := t.isLt
    change 2 * (t.val+1) ≤ m
    omega
  · apply (rotate_valid _ _).2
    apply (valid_one _).2
    have ht := t.isLt
    change t.val+1 < m
    omega
  · apply (rotate_valid _ _).2
    have ht := t.isLt
    have hu := u.isLt
    apply (valid_two _ _ (by simp [uParam, vParam]; omega)).2
    simp [uParam, vParam]
    omega

private def mask {m : ℕ} (p : Fin 5 → Offset m) : ℕ :=
  ∑ i : Fin 5, match p i with
    | .inl _ => 0
    | .inr _ => 2^i.val

private abbrev Kind := Unit ⊕ (Unit ⊕ (Fin 5 ⊕ Fin 5))

private def kind {m : ℕ} : Choices m → Kind
  | .inl _ => .inl ()
  | .inr (.inl _) => .inr (.inl ())
  | .inr (.inr (.inl (r,_))) => .inr (.inr (.inl r))
  | .inr (.inr (.inr (r,_))) => .inr (.inr (.inr r))

private def code : Kind → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 31
  | .inr (.inr (.inl r)) => 2^((4-r : Fin 5).val)
  | .inr (.inr (.inr r)) => 2^((3-r : Fin 5).val)+2^((4-r : Fin 5).val)

private theorem code_inj : Function.Injective code := by
  intro x y
  revert x y
  decide

private theorem mask_render {m : ℕ} (q : Choices m) : mask (render m q) = code (kind q) := by
  rcases q with t | t | ⟨r,t⟩ | ⟨r,⟨t,u⟩⟩
  · simp [mask, render, code, kind]
  · norm_num [mask, render, code, kind, Fin.sum_univ_succ]
  · fin_cases r <;> rfl
  · fin_cases r <;> rfl

private theorem render_inj (m : ℕ) : Function.Injective (render m) := by
  intro q w h
  have hk : kind q = kind w := code_inj (by simpa only [mask_render] using congrArg mask h)
  rcases q with t | t | ⟨r,t⟩ | ⟨r,⟨t,u⟩⟩ <;>
    rcases w with s | s | ⟨l,s⟩ | ⟨l,⟨s,v⟩⟩ <;>
    simp only [kind, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl] at hk
  · simpa [render] using congrFun h 0
  · have hh := congrFun h 0
    simp only [render, Sum.inr.injEq] at hh
    have hp := congrArg Fin.val hh
    have hts : t = s := Fin.ext hp
    subst s
    rfl
  · subst l
    have hh := congrFun h (4-r)
    change oneBase m (asB t (by omega)) ((4-r)+r) =
      oneBase m (asB s (by omega)) ((4-r)+r) at hh
    rw [sub_add_cancel] at hh
    change (Sum.inr (asB t (by omega)) : Offset m) = Sum.inr (asB s (by omega)) at hh
    have hp := congrArg Fin.val (Sum.inr.inj hh)
    have hts : t = s := Fin.ext hp
    subst s
    rfl
  · subst l
    have h3 := congrFun h (3-r)
    have h4 := congrFun h (4-r)
    change twoBase m (uParam t u) (vParam t u) ((3-r)+r) =
      twoBase m (uParam s v) (vParam s v) ((3-r)+r) at h3
    change twoBase m (uParam t u) (vParam t u) ((4-r)+r) =
      twoBase m (uParam s v) (vParam s v) ((4-r)+r) at h4
    rw [sub_add_cancel] at h3 h4
    change (Sum.inr (uParam t u) : Offset m) = Sum.inr (uParam s v) at h3
    change (Sum.inr (vParam t u) : Offset m) = Sum.inr (vParam s v) at h4
    have hu := congrArg Fin.val (Sum.inr.inj h3)
    have hv := congrArg Fin.val (Sum.inr.inj h4)
    change u.val = v.val at hu
    change t.val-u.val-1 = s.val-v.val-1 at hv
    have hut := u.isLt
    have hvs := v.isLt
    have hts : t = s := Fin.ext (by omega)
    subst s
    have huv : u = v := Fin.ext hu
    subst v
    rfl

private theorem render_surj {m : ℕ} (hm : 0 < m) :
    Function.Surjective (fun q : Choices m => (⟨render m q,render_valid hm q⟩ :
      {p : Fin 5 → Offset m // Valid m p})) := by
  rintro ⟨p,hp⟩
  rcases classify m p hp.1 with ⟨t,rfl⟩ | ⟨t,rfl⟩ | ⟨r,t,rfl⟩ | ⟨r,u,v,h,rfl⟩
  · exact ⟨.inl t,rfl⟩
  · have ht := (valid_B hm t).1 hp
    exact ⟨.inr (.inl ⟨t.val,by omega⟩),rfl⟩
  · have ht := (valid_one t).1 ((rotate_valid _ _).1 hp)
    exact ⟨.inr (.inr (.inl (r,⟨t.val,by omega⟩))),rfl⟩
  · have ht := (valid_two u v h).1 ((rotate_valid _ _).1 hp)
    let t : Fin (m-1) := ⟨u.val+v.val+1,by omega⟩
    let w : Fin t.val := ⟨u.val,by simp [t]⟩
    have hu : uParam t w = u := rfl
    have hv : vParam t w = v := Fin.ext (by simp [vParam,t,w]; omega)
    refine ⟨.inr (.inr (.inr (r,⟨t,w⟩))), Subtype.ext ?_⟩
    simp only [render,hu,hv]

private theorem count_eq {m : ℕ} (hm : 0 < m) :
    Nat.card {p : Fin 5 → Offset m // Valid m p} =
      (m+1) + m/2 + 5*(m-1) + 5*((m-1)*(m-2)/2) := by
  let f (q : Choices m) : {p : Fin 5 → Offset m // Valid m p} := ⟨render m q, render_valid hm q⟩
  have hi : Function.Injective f := fun q w h => render_inj m (congrArg Subtype.val h)
  have hs : Function.Surjective f := render_surj hm
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩).symm, Nat.card_eq_fintype_card]
  simp only [Choices,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]
  have he : m-1-1 = m-2 := by omega
  rw [he]
  omega

end A128153Proof

namespace A128153Proof

open OMA.S_oeis_a128153

private theorem count_positive (n : ℕ) (hn : 0 < n) :
    a n = n+2+(n+1)/2+5*n+5*(n*(n-1)/2) := by
  rw [a, if_neg (by omega), count_eq (by omega)]
  rw [show n+1-1 = n by omega, show n+1-2 = n-1 by omega]

theorem formula (n : ℕ) (hn : 0 < n) :
    4 * (a n : ℤ) = 10 * (n : ℤ)^2 + 16*n + 9 - (-1 : ℤ)^n := by
  have hn1 : 1 ≤ n := hn
  have hex : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have heven : n * (n-1) % 2 = 0 := by
    rw [Nat.mul_mod]
    rcases hex with h | h
    · simp [h]
    · have hh : (n-1)%2 = 0 := by omega
      simp [hh]
  have hprod : 2 * (n*(n-1)/2) = n*(n-1) := by omega
  have hprod' := congrArg (fun x : ℕ => (x : ℤ)) hprod
  simp only [Int.natCast_mul, Int.natCast_sub hn1] at hprod'
  change (2 : ℤ) * (↑(n*(n-1)/2) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) at hprod'
  rw [count_positive n hn]
  simp only [Int.natCast_add, Int.natCast_mul]
  change 4 * ((n : ℤ) + 2 + (↑((n+1)/2) : ℤ) + 5 * (n : ℤ) +
    5 * (↑(n*(n-1)/2) : ℤ)) = _
  rcases hex with h | h
  · have ht : (2:ℤ) * (↑((n+1)/2):ℤ) = n := by exact_mod_cast (show 2*((n+1)/2)=n by omega)
    have hn2 : n=2*(n/2) := by omega
    have hp : (-1:ℤ)^n = 1 := by nth_rw 1 [hn2]; rw [pow_mul]; norm_num
    rw [hp]
    nlinarith
  · have ht : (2:ℤ) * (↑((n+1)/2):ℤ) = (n : ℤ)+1 := by
      exact_mod_cast (show 2*((n+1)/2)=n+1 by omega)
    have hn2 : n=2*(n/2)+1 := by omega
    have hp : (-1:ℤ)^n = -1 := by nth_rw 1 [hn2]; rw [pow_succ,pow_mul]; norm_num
    rw [hp]
    nlinarith

set_option maxHeartbeats 2000000 in
theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 2 * (a (n - 1) : ℤ) - 2 * (a (n - 3) : ℤ) + a (n - 4) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+5 := ⟨n-5,by omega⟩
  have h5 := formula (k+5) (by omega)
  have h4 := formula (k+4) (by omega)
  have h2 := formula (k+2) (by omega)
  have h1 := formula (k+1) (by omega)
  norm_num [pow_add] at h1 h2 h4 h5
  rw [show k+5-1 = k+4 by omega,show k+5-3 = k+2 by omega,show k+5-4 = k+1 by omega]
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by decide)
  calc
    (4 : ℤ) * (a (k+5) : ℤ) =
        2 * (4 * (a (k+4) : ℤ)) - 2 * (4 * (a (k+2) : ℤ)) + 4 * (a (k+1) : ℤ) := by
      rw [h5,h4,h2,h1]
      ring
    _ = _ := by ring

open PowerSeries in
theorem generating :
    (((X : PowerSeries ℤ) - 1)^3 * (X + 1) * PowerSeries.mk (fun n => (a n : ℤ))) =
      -X^4 + X^3 - 2*X^2 - 7*X - 1 := by
  have hd : (((X : PowerSeries ℤ) - 1)^3 * (X + 1)) =
      -1 + C 2 * X^1 - C 2 * X^3 + X^4 := by norm_num; ring
  have hm : (-X^4 + X^3 - 2*X^2 - 7*X - 1 : PowerSeries ℤ) =
      -X^4 + X^3 - C 2 * X^2 - C 7 * X^1 - X^0 := by norm_num
  rw [hd,hm]
  ext n
  simp only [sub_mul,add_mul,neg_mul,one_mul,mul_assoc,map_neg,map_add,map_sub,
    PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul',PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 4
  · have h0 : a 0 = 1 := by simp [a]
    have h1 : a 1 = 9 := by rw [count_positive 1 (by decide)]
    have h2 : a 2 = 20 := by rw [count_positive 2 (by decide)]
    have h3 : a 3 = 37 := by rw [count_positive 3 (by decide)]
    have h4 : a 4 = 58 := by rw [count_positive 4 (by decide)]
    interval_cases n <;> norm_num [h0,h1,h2,h3,h4]
  simp only [if_pos (show 1 ≤ n by omega),if_pos (show 3 ≤ n by omega),
    if_pos (show 4 ≤ n by omega),if_neg (show n ≠ 4 by omega),if_neg (show n ≠ 3 by omega),
    if_neg (show n ≠ 2 by omega),if_neg (show n ≠ 1 by omega),if_neg (show n ≠ 0 by omega)]
  have hh := recurrence n (by omega)
  omega

theorem solve : type_of% @OMA.S_oeis_a128153.main := ⟨formula,recurrence,generating⟩

end A128153Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a128153.main := A128153Proof.solve
