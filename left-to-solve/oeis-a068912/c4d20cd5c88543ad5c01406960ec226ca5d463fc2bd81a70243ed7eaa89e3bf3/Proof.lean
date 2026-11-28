import OMAStatements.S_oeis_a068912

/-!
Peter Luschny proposed the floor formula in OEIS A068912.
Herbert Kociemba proved it there by bounding the smaller-root term.
Source: https://oeis.org/A068912
-/

namespace A068912Proof

open OMA.S_oeis_a068912

private def bounded (x : ℤ) {n : ℕ} (w : Fin n → Bool) : Prop :=
  ∀ k : Fin (n + 1), -3 ≤ x + partialSum w k.val ∧ x + partialSum w k.val ≤ 3

private instance (x : ℤ) (n : ℕ) : DecidablePred (bounded x (n := n)) := by
  intro w
  unfold bounded
  infer_instance

private noncomputable def num (n : ℕ) (x : ℤ) : ℕ :=
  Fintype.card {w : Fin n → Bool // bounded x w}

private theorem starts_inside {n : ℕ} {x : ℤ} {w : Fin n → Bool} (h : bounded x w) :
    -3 ≤ x ∧ x ≤ 3 := by
  simpa [partialSum] using h 0

private theorem partial_cons {n : ℕ} (b : Bool) (w : Fin n → Bool) (k : ℕ) :
    partialSum (Fin.cons b w) (k + 1) = step b + partialSum w k := by
  unfold partialSum
  rw [Fin.sum_univ_succ]
  simp

private theorem bounded_cons {n : ℕ} (x : ℤ) (b : Bool) (w : Fin n → Bool) :
    bounded x (Fin.cons b w) ↔ (-3 ≤ x ∧ x ≤ 3) ∧ bounded (x + step b) w := by
  constructor
  · intro h
    refine ⟨starts_inside h, ?_⟩
    intro k
    have hk := h k.succ
    change -3 ≤ x + partialSum (Fin.cons b w) (k.val + 1) ∧
      x + partialSum (Fin.cons b w) (k.val + 1) ≤ 3 at hk
    simpa [partial_cons, add_assoc] using hk
  · rintro ⟨hx, h⟩ k
    refine Fin.cases ?_ (fun j => ?_) k
    · simpa [partialSum] using hx
    · change -3 ≤ x + partialSum (Fin.cons b w) (j.val + 1) ∧
        x + partialSum (Fin.cons b w) (j.val + 1) ≤ 3
      simpa [partial_cons, add_assoc] using h j

private noncomputable def consWalk (n : ℕ) (x : ℤ) (hx : -3 ≤ x ∧ x ≤ 3) :
    {w : Fin (n + 1) → Bool // bounded x w} ≃
      Σ b : Bool, {w : Fin n → Bool // bounded (x + step b) w} where
  toFun w :=
    ⟨w.val 0, Fin.tail w.val,
      ((bounded_cons x (w.val 0) (Fin.tail w.val)).1
        ((Fin.cons_self_tail w.val).symm ▸ w.property)).2⟩
  invFun w := ⟨Fin.cons w.1 w.2.val, (bounded_cons x w.1 w.2.val).2 ⟨hx, w.2.property⟩⟩
  left_inv w := Subtype.ext (Fin.cons_self_tail w.val)
  right_inv := by
    rintro ⟨b, w, hw⟩
    rfl

private theorem num_succ (n : ℕ) (x : ℤ) (hx : -3 ≤ x ∧ x ≤ 3) :
    num (n + 1) x = num n (x + 1) + num n (x - 1) := by
  change Fintype.card {w : Fin (n + 1) → Bool // bounded x w} = _
  rw [Fintype.card_congr (consWalk n x hx), Fintype.card_sigma]
  change (∑ b : Bool, num n (x + step b)) = _
  simp [step, sub_eq_add_neg]

private theorem num_outside (n : ℕ) (x : ℤ) (hx : ¬ (-3 ≤ x ∧ x ≤ 3)) : num n x = 0 := by
  let : IsEmpty {w : Fin n → Bool // bounded x w} := ⟨fun w => hx (starts_inside w.property)⟩
  exact Fintype.card_of_isEmpty

private theorem num_zero (x : ℤ) (hx : -3 ≤ x ∧ x ≤ 3) : num 0 x = 1 := by
  let : Unique {w : Fin 0 → Bool // bounded x w} := {
    default := ⟨Fin.elim0, by
      intro k
      simpa [partialSum] using hx⟩
    uniq := fun w => Subtype.ext (funext fun i => Fin.elim0 i) }
  exact Fintype.card_unique

private theorem a_num (n : ℕ) : a n = num n 0 := by
  unfold a num
  simp [Fintype.card_subtype, bounded, stays]

private theorem two_steps (n : ℕ) :
    (num (n + 2) 0 = 2 * num n 0 + (num n 2 + num n (-2))) ∧
    (num (n + 2) 2 + num (n + 2) (-2) = 2 * num n 0 + 2 * (num n 2 + num n (-2))) := by
  have h₀ := num_succ (n + 1) 0 (by decide)
  have h₂ := num_succ (n + 1) 2 (by decide)
  have hneg₂ := num_succ (n + 1) (-2) (by decide)
  have h₁ := num_succ n 1 (by decide)
  have hneg₁ := num_succ n (-1) (by decide)
  have h₃ := num_succ n 3 (by decide)
  have hneg₃ := num_succ n (-3) (by decide)
  have hb₁ := num_outside n 4 (by decide)
  have hb₂ := num_outside n (-4) (by decide)
  norm_num at h₀ h₂ hneg₂ h₁ hneg₁ h₃ hneg₃
  rw [show n + 1 + 1 = n + 2 by omega] at h₀ h₂ hneg₂
  constructor <;> omega

private noncomputable def U (k : ℕ) : ℝ := (1 + Real.sqrt 2) / 2 * (2 + Real.sqrt 2) ^ k
private noncomputable def V (k : ℕ) : ℝ := (1 - Real.sqrt 2) / 2 * (2 - Real.sqrt 2) ^ k

private theorem sqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)

private theorem U_next (k : ℕ) : U (k + 1) = (2 + Real.sqrt 2) * U k := by
  unfold U
  rw [pow_succ]
  ring

private theorem V_next (k : ℕ) : V (k + 1) = (2 - Real.sqrt 2) * V k := by
  unfold V
  rw [pow_succ]
  ring

private theorem model (k e : ℕ) (he : e ≤ 1) :
    ((num (2 * k + e) 0 : ℝ) = ((e : ℝ) + 1) * (U k + V k)) ∧
    ((↑(num (2 * k + e) 2 + num (2 * k + e) (-2)) : ℝ) =
      ((e : ℝ) + 1) * Real.sqrt 2 * (U k - V k)) := by
  induction k with
  | zero =>
      have h₀ := num_zero 0 (by decide)
      have h₂ := num_zero 2 (by decide)
      have hneg₂ := num_zero (-2) (by decide)
      have h₁ := num_zero 1 (by decide)
      have hneg₁ := num_zero (-1) (by decide)
      have h₃ := num_zero 3 (by decide)
      have hneg₃ := num_zero (-3) (by decide)
      have c₀ := num_succ 0 0 (by decide)
      have c₂ := num_succ 0 2 (by decide)
      have cneg₂ := num_succ 0 (-2) (by decide)
      norm_num [h₁, hneg₁, h₃, hneg₃] at c₀ c₂ cneg₂
      interval_cases e <;> constructor <;>
        norm_num [h₀, h₂, hneg₂, c₀, c₂, cneg₂, U, V]
      all_goals nlinarith [sqrt_sq]
  | succ k ih =>
      have hk : 2 * (k + 1) + e = (2 * k + e) + 2 := by omega
      rcases two_steps (2 * k + e) with ⟨hc, hs⟩
      constructor
      · rw [hk, hc, U_next, V_next]
        push_cast at *
        rw [ih.1, ih.2]
        ring
      · rw [hk, hs, U_next, V_next]
        push_cast at *
        rw [ih.1, ih.2]
        linear_combination (-((e : ℝ) + 1) * (U k + V k)) * sqrt_sq

private theorem sqrt_bounds : 1 < Real.sqrt 2 ∧ Real.sqrt 2 < 2 := by
  have hp := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith [sqrt_sq]

private theorem luschny_even (k : ℕ) : luschny (2 * k) = U k := by
  have he : (((2 * k : ℕ) : ℝ) / 2) = (k : ℝ) := by push_cast; ring
  have hsign : (-1 : ℝ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
  rw [luschny, he, Real.rpow_natCast, hsign]
  unfold U r
  ring

private theorem luschny_odd (k : ℕ) : luschny (2 * k + 1) = 2 * U k := by
  let L := 2 + Real.sqrt (2 : ℝ)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have he : (((2 * k + 1 : ℕ) : ℝ) / 2) = (k : ℝ) + 1 / 2 := by push_cast; ring
  have hsign : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  have hproduct : Real.sqrt L * Real.sqrt (2 * L) = Real.sqrt 2 * L := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ = Real.sqrt 2 * (Real.sqrt L ^ 2) := by ring
      _ = _ := by rw [Real.sq_sqrt hL]
  have hmul : L ^ ((k : ℝ) + 1 / 2) = L ^ k * Real.sqrt L := by
    rw [Real.rpow_add (by dsimp [L]; positivity), Real.rpow_natCast, Real.sqrt_eq_rpow]
  rw [luschny, he, hsign]
  have hbase : 1 + r = L := by unfold r L; ring
  rw [hbase, hmul]
  calc
    _ = L ^ k * (Real.sqrt L * Real.sqrt (2 * L)) / 2 := by ring
    _ = _ := by
      rw [hproduct]
      unfold U L
      linear_combination ((2 + Real.sqrt 2) ^ k / 2) * sqrt_sq

private theorem floor_model (n : ℕ) : (a n : ℤ) = ⌊luschny n⌋ := by
  let k := n / 2
  let e := n % 2
  have he : e ≤ 1 := by dsimp [e]; omega
  have hn : n = 2 * k + e := by dsimp [k, e]; omega
  have form : luschny (2 * k + e) = ((e : ℝ) + 1) * U k := by
    interval_cases e
    · simpa using luschny_even k
    · simpa only [Nat.cast_one, one_add_one_eq_two] using luschny_odd k
  have count : (a (2 * k + e) : ℝ) = ((e : ℝ) + 1) * (U k + V k) := by
    rw [a_num]
    exact (model k e he).1
  have hq₀ : 0 ≤ 2 - Real.sqrt (2 : ℝ) := by linarith [sqrt_bounds.2]
  have hq₁ : 2 - Real.sqrt (2 : ℝ) ≤ 1 := by linarith [sqrt_bounds.1]
  have hp₀ : 0 ≤ (2 - Real.sqrt (2 : ℝ)) ^ k := pow_nonneg hq₀ _
  have hp₁ : (2 - Real.sqrt (2 : ℝ)) ^ k ≤ 1 := pow_le_one₀ hq₀ hq₁
  have he' : (e : ℝ) ≤ 1 := by exact_mod_cast he
  have hd₀ : 0 ≤ (Real.sqrt (2 : ℝ) - 1) / 2 := by linarith [sqrt_bounds.1]
  have hfactor : ((e : ℝ) + 1) * ((Real.sqrt (2 : ℝ) - 1) / 2) ≤
      2 * ((Real.sqrt (2 : ℝ) - 1) / 2) := by gcongr; linarith
  have hgap : 0 ≤ -((e : ℝ) + 1) * V k ∧ -((e : ℝ) + 1) * V k < 1 := by
    have hform : -((e : ℝ) + 1) * V k =
        (((e : ℝ) + 1) * ((Real.sqrt (2 : ℝ) - 1) / 2)) * (2 - Real.sqrt 2) ^ k := by
      unfold V
      ring
    rw [hform]
    have hnonneg : 0 ≤ ((e : ℝ) + 1) * ((Real.sqrt (2 : ℝ) - 1) / 2) :=
      mul_nonneg (by positivity) hd₀
    exact ⟨mul_nonneg hnonneg hp₀, (mul_le_of_le_one_right hnonneg hp₁).trans_lt
      (hfactor.trans_lt (by linarith [sqrt_bounds.2]))⟩
  rw [hn]
  symm
  apply Int.floor_eq_iff.mpr
  push_cast
  rw [form, count]
  constructor <;> linarith [hgap.1, hgap.2]

end A068912Proof

open A068912Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a068912.main := floor_model
