import OMAStatements.S_oeis_a097509

/-!
The OEIS identity was proved by Schaeffer, Shallit and Zorcic in arXiv:2402.08331.
This proof checks the Beatty floors directly.
-/

namespace A097509Proof

open OMA.S_oeis_a097509

private noncomputable def alpha : ℝ := 1 + Real.sqrt 2
private noncomputable def beta : ℝ := Real.sqrt 2 - 1

private theorem sqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
private theorem beta_bounds : (2 / 5 : ℝ) < beta ∧ beta < 1 / 2 := by
  have h := Real.sqrt_nonneg (2 : ℝ)
  unfold beta
  constructor <;> nlinarith [sqrt_sq]

private theorem alpha_eq : alpha = 2 + beta := by unfold alpha beta; ring
private theorem alpha_beta : alpha * beta = 1 := by
  unfold alpha beta
  linear_combination sqrt_sq

private theorem base_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * alpha :=
  mul_nonneg (by positivity) (by linarith [alpha_eq, beta_bounds.1])

private theorem not_integer (n : ℕ) (hn : 0 < n) (z : ℤ) : (n : ℝ) * alpha ≠ z := by
  have ha : Irrational alpha := by
    unfold alpha
    simpa using irrational_sqrt_two.ratCast_add (1 : ℚ)
  intro hz
  apply ha.natCast_mul hn.ne'
  refine ⟨(z : ℚ), ?_⟩
  push_cast
  exact hz.symm

private noncomputable def B (n : ℕ) : ℕ := ⌊(n : ℝ) * alpha⌋₊

private theorem certify (n q : ℕ) (h₀ : (q : ℝ) ≤ (n : ℝ) * alpha)
    (h₁ : (n : ℝ) * alpha < (q : ℝ) + 1) : B n = q :=
  (Nat.floor_eq_iff (base_nonneg n)).mpr ⟨h₀, h₁⟩

private theorem bracket (n : ℕ) : (B n : ℝ) ≤ (n : ℝ) * alpha ∧
    (n : ℝ) * alpha < (B n : ℝ) + 1 :=
  (Nat.floor_eq_iff (base_nonneg n)).mp rfl

private theorem B_mono : Monotone B := by
  intro m n h
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (by linarith [alpha_eq, beta_bounds.1])

private theorem freq_eq (n : ℕ) (hn : 0 < n) : frequency n = B (n + 1) - B n := by
  classical
  have hα : 0 < alpha := by linarith [alpha_eq, beta_bounds.1]
  have hβ : 0 < beta := by linarith [beta_bounds.1]
  have cast_floor (k : ℕ) :
      ⌊(k : ℝ) * Real.sqrt 2⌋ - (k : ℤ) = (n : ℤ) ↔
        (n : ℝ) ≤ (k : ℝ) * beta ∧ (k : ℝ) * beta < (n : ℝ) + 1 := by
    rw [sub_eq_iff_eq_add, Int.floor_eq_iff]
    push_cast
    unfold beta
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have scaled (k : ℕ) :
      ((n : ℝ) ≤ (k : ℝ) * beta ∧ (k : ℝ) * beta < (n : ℝ) + 1) ↔
      ((n : ℝ) * alpha ≤ (k : ℝ) ∧ (k : ℝ) < ((n + 1 : ℕ) : ℝ) * alpha) := by
    have hb (x : ℝ) : (x * beta) * alpha = x := by rw [mul_assoc, mul_comm beta alpha, alpha_beta, mul_one]
    have ha (x : ℝ) : (x * alpha) * beta = x := by rw [mul_assoc, alpha_beta, mul_one]
    push_cast
    constructor
    · intro h
      exact ⟨by simpa only [hb] using mul_le_mul_of_nonneg_right h.1 hα.le,
        by simpa only [hb] using mul_lt_mul_of_pos_right h.2 hα⟩
    · intro h
      exact ⟨by simpa only [ha] using mul_le_mul_of_nonneg_right h.1 hβ.le,
        by simpa only [ha] using mul_lt_mul_of_pos_right h.2 hβ⟩
  have integer_interval (k : ℕ) :
      ((n : ℝ) * alpha ≤ (k : ℝ) ∧ (k : ℝ) < ((n + 1 : ℕ) : ℝ) * alpha) ↔
        B n < k ∧ k ≤ B (n + 1) := by
    have hne : (n : ℝ) * alpha ≠ (k : ℝ) := by simpa using not_integer n hn (k : ℤ)
    have hne' : ((n + 1 : ℕ) : ℝ) * alpha ≠ (k : ℝ) := by
      simpa using not_integer (n + 1) (by omega) (k : ℤ)
    constructor
    · intro h
      exact ⟨(Nat.floor_lt (base_nonneg n)).mpr (lt_of_le_of_ne h.1 hne),
        (Nat.le_floor_iff (base_nonneg (n + 1))).mpr h.2.le⟩
    · intro h
      exact ⟨((Nat.floor_lt (base_nonneg n)).mp h.1).le,
        lt_of_le_of_ne ((Nat.le_floor_iff (base_nonneg (n + 1))).mp h.2) hne'.symm⟩
  let P := fun k : ℕ => ⌊(k : ℝ) * Real.sqrt 2⌋ - (k : ℤ) = (n : ℤ)
  have hset : (Finset.range (3 * (n + 1))).filter P = Finset.Ioc (B n) (B (n + 1)) := by
    ext k
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    have h : P k ↔ B n < k ∧ k ≤ B (n + 1) :=
      (cast_floor k).trans ((scaled k).trans (integer_interval k))
    rw [h]
    refine ⟨fun h' => h'.2, fun h' => ⟨?_, h'⟩⟩
    have hK := ((integer_interval k).mpr h').2
    have hα₃ : alpha < 3 := by linarith [alpha_eq, beta_bounds.2]
    have hv := mul_lt_mul_of_pos_left hα₃ (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by positivity)
    exact_mod_cast hK.trans (hv.trans_eq (mul_comm _ _))
  unfold frequency
  change ((Finset.range (3 * (n + 1))).filter P).card = _
  rw [hset, Nat.card_Ioc]

private noncomputable def signal (n : ℕ) : ℕ := frequency (n + 1)

private theorem signal_eq (n : ℕ) : signal n = B (n + 2) - B (n + 1) := freq_eq _ (by omega)

private theorem initial₁ : B 2 = 4 := certify 2 4 (by norm_num; linarith [alpha_eq, beta_bounds.1])
  (by norm_num; linarith [alpha_eq, beta_bounds.2])
private theorem initial₂ : B 3 = 7 := certify 3 7 (by norm_num; linarith [alpha_eq, beta_bounds.1])
  (by norm_num; linarith [alpha_eq, beta_bounds.2])
private theorem initial₃ : B 4 = 9 := certify 4 9 (by norm_num; linarith [alpha_eq, beta_bounds.1])
  (by norm_num; linarith [alpha_eq, beta_bounds.2])

private theorem alphabet (n : ℕ) : signal n = 2 ∨ signal n = 3 := by
  rw [signal_eq]
  have h := bracket (n + 1)
  have h' := bracket (n + 2)
  push_cast at h h'
  have hl : (B (n + 1) : ℝ) + 1 < B (n + 2) := by
    linarith [h.1, h'.2, alpha_eq, beta_bounds.1]
  have hu : (B (n + 2) : ℝ) < B (n + 1) + 4 := by
    linarith [h.2, h'.1, alpha_eq, beta_bounds.2]
  have hl' : B (n + 1) + 1 < B (n + 2) := by exact_mod_cast hl
  have hu' : B (n + 2) < B (n + 1) + 4 := by exact_mod_cast hu
  omega

private theorem sums (n : ℕ) : sumFirst signal n = B (n + 2) - 4 := by
  induction n with
  | zero => simp [sumFirst, initial₁]
  | succ n ih =>
      unfold sumFirst at *
      rw [Finset.sum_range_succ, ih, signal_eq]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      have h := B_mono (show 2 ≤ n + 2 by omega)
      have h' := B_mono (show n + 2 ≤ n + 3 by omega)
      rw [initial₁] at h
      omega

private theorem positions (n : ℕ) (hn : 1 ≤ n) :
    signal (sumFirst signal n) = signal n ∧
    signal (sumFirst signal n + 1) = 5 - signal (sumFirst signal n) ∧
    (signal (n + 1) = 3 →
      signal (sumFirst signal n + 2) = 5 - signal (sumFirst signal n + 1)) := by
  let t := n + 2
  let b := B t
  let delta : ℝ := (t : ℝ) * alpha - (b : ℝ)
  let q := 2 * b + t
  have ht : 3 ≤ t := by dsimp [t]; omega
  have hb : 7 ≤ b := by
    exact initial₂ ▸ B_mono ht
  have hq : 8 ≤ q := by dsimp [q]; omega
  have hdelta₀ : 0 < delta := by
    have hne := not_integer t (by omega) (b : ℤ)
    push_cast at hne
    exact sub_pos.mpr (lt_of_le_of_ne (bracket t).1 hne.symm)
  have hdelta₁ : delta < 1 := by dsimp [delta, b]; linarith [(bracket t).2]
  have hne : delta ≠ beta := by
    intro he
    apply not_integer (t - 1) (by omega) ((b : ℤ) - 2)
    push_cast [Nat.cast_sub (show 1 ≤ t by omega)]
    dsimp [delta] at he
    linarith [alpha_eq]
  have shift_value : (b : ℝ) * alpha = (q : ℝ) - beta * delta := by
    dsimp [q, delta]
    push_cast
    unfold alpha beta
    linear_combination (t : ℝ) * sqrt_sq
  have translate (c : ℕ) (hc : c ≤ b) :
      ((b - c : ℕ) : ℝ) * alpha = (q : ℝ) - 2 * c - beta * (delta + c) := by
    rw [Nat.cast_sub hc, sub_mul, shift_value]
    unfold alpha beta
    ring
  have nested (c d : ℕ) (hc : c ≤ b) (hd : 2 * c + d ≤ q)
      (hlo : (d : ℝ) - 1 < beta * (delta + c))
      (hhi : beta * (delta + c) ≤ (d : ℝ)) :
      B (b - c) = q - (2 * c + d) := by
    apply certify <;> rw [translate c hc, Nat.cast_sub hd] <;> push_cast <;> linarith
  have hβ : 0 < beta := by linarith [beta_bounds.1]
  have prod_bounds (c : ℝ) : beta * c < beta * (delta + c) ∧
      beta * (delta + c) < beta * (c + 1) :=
    ⟨mul_lt_mul_of_pos_left (by linarith) hβ, mul_lt_mul_of_pos_left (by linarith) hβ⟩
  have b₀ : B b = q - 1 := by
    have p := prod_bounds 0
    norm_num at p
    simpa using nested 0 1 (by omega) (by omega) (by norm_num; linarith)
      (by norm_num; linarith [beta_bounds.2, p.2])
  have b₁ : B (b - 1) = q - 3 := by
    have p := prod_bounds 1
    norm_num at p
    simpa using nested 1 1 (by omega) (by omega) (by norm_num; linarith)
      (by norm_num; linarith [beta_bounds.2, p.2])
  have b₃ : B (b - 3) = q - 8 := by
    have p := prod_bounds 3
    norm_num at p
    simpa using nested 3 2 (by omega) (by omega)
      (by norm_num; linarith [beta_bounds.1, p.1])
      (by norm_num; linarith [beta_bounds.2, p.2])
  have boundary : beta * (delta + 2) - 1 = beta * (delta - beta) := by
    unfold beta
    linear_combination sqrt_sq
  have from_sum (j : ℕ) (hj : j ≤ 2) :
      signal (sumFirst signal n + j) = B (b - (2 - j)) - B (b - (3 - j)) := by
    rw [signal_eq, sums]
    change B (b - 4 + j + 2) - B (b - 4 + j + 1) = _
    rw [show b - 4 + j + 2 = b - (2 - j) by omega,
      show b - 4 + j + 1 = b - (3 - j) by omega]
  have s₀ := from_sum 0 (by decide)
  have s₁ := from_sum 1 (by decide)
  have s₂ := from_sum 2 (by decide)
  norm_num at s₀ s₁ s₂
  have prev : ((t - 1 : ℕ) : ℝ) * alpha = (b : ℝ) - 2 + (delta - beta) := by
    rw [Nat.cast_sub (by omega : 1 ≤ t)]
    dsimp [delta]
    norm_num only [Nat.cast_one]
    linear_combination -alpha_eq
  have sig : signal n = b - B (t - 1) := signal_eq n
  by_cases hlow : delta < beta
  · have p := prod_bounds 2
    have b₂ : B (b - 2) = q - 5 := by
      simpa using nested 2 1 (by omega) (by omega)
        (by norm_num; nlinarith [p.1, hβ])
        (by norm_num; nlinarith [mul_neg_of_pos_of_neg hβ (sub_neg.mpr hlow), boundary])
    have before : B (t - 1) = b - 3 := by
      apply certify <;> rw [prev, Nat.cast_sub (by omega : 3 ≤ b)] <;> norm_num <;>
        linarith [hdelta₀, beta_bounds.2]
    have after : B (t + 1) = b + 2 := by
      have eval : ((t + 1 : ℕ) : ℝ) * alpha = b + 2 + (delta + beta) := by
        dsimp [delta]
        push_cast
        linarith [alpha_eq]
      apply certify <;> rw [eval] <;> push_cast <;> linarith [beta_bounds.2]
    have hnext : signal (n + 1) = 2 := by
      rw [signal_eq]
      change B (t + 1) - b = 2
      rw [after]
      omega
    rw [b₂, b₃] at s₀
    rw [b₁, b₂] at s₁
    rw [before] at sig
    refine ⟨by omega, by omega, ?_⟩
    omega
  · have hhigh : beta < delta := lt_of_le_of_ne (le_of_not_gt hlow) hne.symm
    have p := prod_bounds 2
    have b₂ : B (b - 2) = q - 6 := by
      simpa using nested 2 2 (by omega) (by omega)
        (by norm_num; nlinarith [mul_pos hβ (sub_pos.mpr hhigh), boundary])
        (by norm_num; nlinarith [p.2, beta_bounds.2])
    have before : B (t - 1) = b - 2 := by
      apply certify <;> rw [prev, Nat.cast_sub (by omega : 2 ≤ b)] <;> norm_num <;>
        linarith [hdelta₁, hβ]
    rw [b₂, b₃] at s₀
    rw [b₁, b₂] at s₁
    rw [b₀, b₁] at s₂
    rw [before] at sig
    exact ⟨by omega, by omega, fun _ => by omega⟩

theorem result : FollowsRule signal := by
  refine ⟨?_, ?_, fun n _ => alphabet n, fun n hn => (positions n hn).1, ?_⟩
  · rw [signal_eq, initial₂, initial₁]
  · rw [signal_eq, initial₃, initial₂]
  · intro n j hn hj hlt
    have ha := alphabet (n + 1)
    have hb : j = 1 ∨ j = 2 := by omega
    rcases hb with rfl | rfl
    · simpa using (positions n hn).2.1
    · have hnext : signal (n + 1) = 3 := by omega
      have hpos := (positions n hn).2.2 hnext
      simpa [show sumFirst signal n + 2 - 1 = sumFirst signal n + 1 by omega] using hpos

end A097509Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a097509.main := A097509Proof.result
