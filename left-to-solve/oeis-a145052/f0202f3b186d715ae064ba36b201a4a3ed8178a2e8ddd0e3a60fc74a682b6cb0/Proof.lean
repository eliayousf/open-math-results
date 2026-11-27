import OMAStatements.S_oeis_a145052

namespace A145052Proof

open BigOperators
open OMA.S_oeis_a145052

private abbrev Array (n : ℕ) := Fin n → Fin n → Fin 2

private def slot {n : ℕ} (i : ℕ) (hi : i + 2 < n) (r : Fin 3) : Fin n :=
  ⟨i + r, by omega⟩

private theorem slot_contains {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    ∃ (j : ℕ) (hj : j + 2 < n) (r : Fin 3), slot j hj r = i := by
  let j := min i.val (n - 3)
  have hj : j + 2 < n := by dsimp [j]; omega
  have hr : i.val - j < 3 := by dsimp [j]; omega
  refine ⟨j, hj, ⟨i.val - j, hr⟩, Fin.ext ?_⟩
  change j + (i.val - j) = i.val
  dsimp [j]
  omega

private theorem slot_residue {n : ℕ} (i : ℕ) (hi : i + 2 < n) (u : Fin 3) :
    ∃! r : Fin 3, (slot i hi r).val % 3 = u.val := by
  refine ⟨⟨(u.val + 3 - i % 3) % 3, by omega⟩, ?_, ?_⟩
  · unfold slot
    have hu := u.isLt
    dsimp
    omega
  · intro r hr
    have hu := u.isLt
    have h := r.isLt
    apply Fin.ext
    change (i + r.val) % 3 = u.val at hr
    dsimp
    omega

private theorem stream {n : ℕ} (hn : 3 ≤ n) (s : Fin n → ℕ)
    (hs : ∀ i : ℕ, ∀ hi : i + 2 < n, (∑ k : Fin 3, s (slot i hi k)) = 1) :
    ∃ r : Fin 3, ∀ j : Fin n, s j = if j.val % 3 = r.val then 1 else 0 := by
  have h0 : 0 + 2 < n := by omega
  have hfirst := hs 0 h0
  simp only [Fin.sum_univ_three] at hfirst
  have hexists (r : Fin 3) (hr : s (slot 0 h0 r) = 1) :
      ∀ j : Fin n, s j = if j.val % 3 = r.val then 1 else 0 := by
    have hseed (j : ℕ) (hj : j < 3) :
        s ⟨j, by omega⟩ = if j % 3 = r.val then 1 else 0 := by
      fin_cases r <;> interval_cases j <;> simp_all [slot] <;> omega
    have aux (j : ℕ) (hj : j < n) : s ⟨j, hj⟩ = if j % 3 = r.val then 1 else 0 := by
      induction j using Nat.strong_induction_on with
      | h j ih =>
        by_cases h : j < 3
        · exact hseed j h
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 3 := ⟨j - 3, by omega⟩
        have ha := hs i (by omega)
        have hb := hs (i + 1) (by omega)
        simp only [Fin.sum_univ_three] at ha hb
        have hstep : s ⟨i + 3, hj⟩ = s ⟨i, by omega⟩ := by
          simp only [slot, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero,
            Nat.add_assoc, Nat.reduceAdd] at ha hb
          omega
        rw [hstep, ih i (by omega) (by omega)]
        have hmod : (i + 3) % 3 = i % 3 := by omega
        rw [hmod]
    exact fun j => aux j.val j.isLt
  have hcases : s (slot 0 h0 0) = 1 ∨ s (slot 0 h0 1) = 1 ∨ s (slot 0 h0 2) = 1 := by omega
  rcases hcases with h | h | h
  · exact ⟨0, hexists 0 h⟩
  · exact ⟨1, hexists 1 h⟩
  · exact ⟨2, hexists 2 h⟩

private def transpose {n : ℕ} (a : Array n) : Array n := fun i j => a j i

private theorem valid_transpose {n : ℕ} {a : Array n} (ha : Valid a) : Valid (transpose a) := by
  intro i j hi hj
  change (∑ r : Fin 3, ∑ c : Fin 3, (a (slot j hj c) (slot i hi r)).val) = 1
  rw [Finset.sum_comm]
  exact ha j i hj hi

private def colSum {n : ℕ} (a : Array n) (i : ℕ) (hi : i + 2 < n) (j : Fin n) : ℕ :=
  ∑ r : Fin 3, (a (slot i hi r) j).val

private theorem strip {n : ℕ} {a : Array n} (ha : Valid a) (hn : 3 ≤ n)
    (i : ℕ) (hi : i + 2 < n) :
    ∃ u : Fin 3, ∀ j : Fin n, colSum a i hi j = if j.val % 3 = u.val then 1 else 0 := by
  apply stream hn (colSum a i hi)
  intro j hj
  unfold colSum
  rw [Finset.sum_comm]
  exact ha i j hi hj

private abbrev ColumnChoice (n : ℕ) (r : Fin 3) := {j : Fin n // j.val % 3 = r.val}

private abbrev Data (n : ℕ) := Σ r : Fin 3, ColumnChoice n r → Fin 3

private def vArray {n : ℕ} (d : Data n) : Array n := fun i j =>
  if hj : j.val % 3 = d.1.val then
    if i.val % 3 = (d.2 ⟨j, hj⟩).val then 1 else 0
  else 0

private theorem residue_sum {n : ℕ} (i : ℕ) (hi : i + 2 < n) (u : Fin 3) :
    (∑ r : Fin 3, if (slot i hi r).val % 3 = u.val then (1 : ℕ) else 0) = 1 := by
  obtain ⟨r, hr, hu⟩ := slot_residue i hi u
  rw [Finset.sum_eq_single r]
  · simp [hr]
  · intro s _ hs
    have H : ¬ (slot i hi s).val % 3 = u.val := fun h => hs (hu s h)
    simp [H]
  · simp

private theorem colSum_vArray {n : ℕ} (d : Data n) (i : ℕ) (hi : i + 2 < n) (j : Fin n) :
    colSum (vArray d) i hi j = if j.val % 3 = d.1.val then 1 else 0 := by
  by_cases h : j.val % 3 = d.1.val
  · simpa [colSum, vArray, h, apply_ite Fin.val] using residue_sum i hi (d.2 ⟨j, h⟩)
  · simp [colSum, vArray, h]

private theorem valid_vArray {n : ℕ} (d : Data n) : Valid (vArray d) := by
  intro i j hi hj
  change (∑ r : Fin 3, ∑ c : Fin 3, (vArray d (slot i hi r) (slot j hj c)).val) = 1
  rw [Finset.sum_comm]
  change (∑ c : Fin 3, colSum (vArray d) i hi (slot j hj c)) = 1
  simp only [colSum_vArray]
  exact residue_sum j hj d.1

private theorem vArray_of_strips {n : ℕ} (hn : 3 ≤ n) (a : Array n) (u : Fin 3)
    (h : ∀ i : ℕ, ∀ hi : i + 2 < n, ∀ j : Fin n,
      colSum a i hi j = if j.val % 3 = u.val then 1 else 0) :
    ∃ d : Data n, a = vArray d := by
  classical
  have hs (j : ColumnChoice n u) :
      ∃ r : Fin 3, ∀ i : Fin n, (a i j.val).val = if i.val % 3 = r.val then 1 else 0 := by
    apply stream hn (fun i => (a i j.val).val)
    intro i hi
    change colSum a i hi j.val = 1
    simpa [j.property] using h i hi j.val
  refine ⟨⟨u, fun j => Classical.choose (hs j)⟩, ?_⟩
  funext i j
  apply Fin.ext
  by_cases hj : j.val % 3 = u.val
  · simpa [vArray, hj, apply_ite Fin.val] using Classical.choose_spec (hs ⟨j, hj⟩) i
  · have hnz : (a i j).val = 0 := by
      obtain ⟨k, hk, r, hr⟩ := slot_contains hn i
      have hc : colSum a k hk j = 0 := by simpa [hj] using h k hk j
      have hle : (a (slot k hk r) j).val ≤ colSum a k hk j := by
        exact Finset.single_le_sum (f := fun r : Fin 3 => (a (slot k hk r) j).val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
      rw [hr, hc] at hle
      omega
    simpa [vArray, hj] using hnz

private theorem array_cases {n : ℕ} (hn : 3 ≤ n) (a : Array n) (ha : Valid a) :
    (∃ d : Data n, a = vArray d) ∨ (∃ d : Data n, a = transpose (vArray d)) := by
  classical
  let u (i : ℕ) (hi : i + 2 < n) := Classical.choose (strip ha hn i hi)
  have hu (i : ℕ) (hi : i + 2 < n) (j : Fin n) :
      colSum a i hi j = if j.val % 3 = (u i hi).val then 1 else 0 := by
    exact Classical.choose_spec (strip ha hn i hi) j
  have hz : 0 + 2 < n := by omega
  by_cases all_equal : ∀ i : ℕ, ∀ hi : i + 3 < n,
      u i (by omega) = u (i + 1) (by omega)
  · have constant (i : ℕ) (hi : i + 2 < n) : u i hi = u 0 hz := by
      induction i with
      | zero => rfl
      | succ i ih =>
        have h := all_equal i (by omega)
        exact h.symm.trans (ih (by omega))
    apply Or.inl
    apply vArray_of_strips hn a (u 0 hz)
    intro i hi j
    rw [hu i hi, constant i hi]
  · push Not at all_equal
    obtain ⟨i, hi, hne⟩ := all_equal
    let first : Fin n := ⟨i, by omega⟩
    let r := u i (by omega)
    have first_one (j : Fin n) (hj : j.val % 3 = r.val) : (a first j).val = 1 := by
      have h₀ := hu i (by omega) j
      have h₁ := hu (i + 1) (by omega) j
      rw [if_pos hj] at h₀
      have hneq : j.val % 3 ≠ (u (i + 1) (by omega)).val := by
        intro h
        apply hne
        exact Fin.ext (hj.symm.trans h)
      rw [if_neg hneq] at h₁
      simp only [colSum, Fin.sum_univ_three, slot, Fin.val_zero, Fin.val_one, Fin.val_two,
        Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at h₀ h₁
      change (a ⟨i, by omega⟩ j).val = 1
      omega
    let s : Fin 3 := ⟨i % 3, by omega⟩
    have flipped (j : ℕ) (hj : j + 2 < n) (k : Fin n) :
        colSum (transpose a) j hj k = if k.val % 3 = s.val then 1 else 0 := by
      obtain ⟨t, ht, _⟩ := slot_residue j hj r
      have h₁ := first_one (slot j hj t) ht
      have hle : (transpose a (slot j hj t) first).val ≤ colSum (transpose a) j hj first := by
        exact Finset.single_le_sum (f := fun t : Fin 3 => (transpose a (slot j hj t) first).val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      change (a first (slot j hj t)).val ≤ _ at hle
      rw [h₁] at hle
      obtain ⟨candidate, hcandidate⟩ := strip (valid_transpose ha) hn j hj
      have hr : first.val % 3 = candidate.val := by
        by_contra off
        rw [hcandidate first, if_neg off] at hle
        omega
      rw [hcandidate k, ← hr]
    obtain ⟨d, hd⟩ := vArray_of_strips hn (transpose a) s flipped
    exact Or.inr ⟨d, congrArg transpose hd⟩

private theorem vArray_injective {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (@vArray n) := by
  rintro ⟨r, f⟩ ⟨s, g⟩ same
  let j : Fin n := ⟨r.val, by omega⟩
  have hr : j.val % 3 = r.val := Nat.mod_eq_of_lt r.isLt
  have h₀ := colSum_vArray (n := n) ⟨r, f⟩ 0 (by omega) j
  have h₁ := colSum_vArray (n := n) ⟨s, g⟩ 0 (by omega) j
  rw [same] at h₀
  have h : r = s := by
    apply Fin.ext
    by_contra hne
    simp [hr, hne] at h₀ h₁
    omega
  subst s
  congr 1
  funext k
  let i : Fin n := ⟨(f k).val, by omega⟩
  have hrs : i.val % 3 = (f k).val := Nat.mod_eq_of_lt (f k).isLt
  have hs := congrFun (congrFun same i) k.val
  change (if hf : k.val.val % 3 = r.val then
      if i.val % 3 = (f ⟨k.val, hf⟩).val then (1 : Fin 2) else 0 else 0) =
    (if hg : k.val.val % 3 = r.val then
      if i.val % 3 = (g ⟨k.val, hg⟩).val then (1 : Fin 2) else 0 else 0) at hs
  have hk : (⟨k.val, k.property⟩ : ColumnChoice n r) = k := rfl
  apply Fin.ext
  by_contra hnfg
  simp [k.property, hk, hrs, hnfg] at hs

private def grid {n : ℕ} (p : Fin 3 × Fin 3) : Array n := vArray ⟨p.1, fun _ => p.2⟩

private theorem grid_transpose {n : ℕ} (r s : Fin 3) :
    transpose (@grid n (r, s)) = grid (s, r) := by
  funext i j
  by_cases hi : i.val % 3 = r.val <;> by_cases hj : j.val % 3 = s.val <;>
    simp [grid, transpose, vArray, hi, hj]

private theorem grid_injective {n : ℕ} (hn : 3 ≤ n) : Function.Injective (@grid n) := by
  rintro ⟨r, s⟩ ⟨t, u⟩ h
  have hr : r = t := congrArg Sigma.fst (vArray_injective hn h)
  have hs : s = u := by
    have hh := congrArg transpose h
    rw [grid_transpose, grid_transpose] at hh
    exact congrArg Sigma.fst (vArray_injective hn hh)
  exact Prod.ext hr hs

private theorem vArray_eq_grid {n : ℕ} (hn : 3 ≤ n) (d e : Data n)
    (h : vArray d = transpose (vArray e)) : vArray d = grid (d.1, e.1) := by
  have hr (j : ColumnChoice n d.1) : (d.2 j).val = e.1.val := by
    let i : Fin n := ⟨(d.2 j).val, by omega⟩
    have hi : i.val % 3 = (d.2 j).val := Nat.mod_eq_of_lt (d.2 j).isLt
    have hs := congrFun (congrFun h i) j.val
    by_contra hne
    simp [vArray, transpose, j.property, hi, hne] at hs
  funext i j
  by_cases hj : j.val % 3 = d.1.val
  · have H := hr ⟨j, hj⟩
    simp [vArray, grid, hj, H]
  · simp [vArray, grid, hj]

private noncomputable def vertical (n : ℕ) : Finset (Array n) := by
  classical exact Finset.univ.image vArray

private noncomputable def horizontal (n : ℕ) : Finset (Array n) := by
  classical exact Finset.univ.image (transpose ∘ vArray)

private noncomputable def grids (n : ℕ) : Finset (Array n) := by
  classical exact Finset.univ.image grid

private theorem mem_vertical {n : ℕ} {a : Array n} :
    a ∈ vertical n ↔ ∃ d : Data n, a = vArray d := by
  classical
  simp [vertical, eq_comm]

private theorem mem_horizontal {n : ℕ} {a : Array n} :
    a ∈ horizontal n ↔ ∃ d : Data n, a = transpose (vArray d) := by
  classical
  simp [horizontal, eq_comm]

private theorem inter_eq_grids (n : ℕ) (hn : 3 ≤ n) [DecidableEq (Array n)] :
    vertical n ∩ horizontal n = grids n := by
  classical
  ext a
  simp only [Finset.mem_inter, mem_vertical, mem_horizontal, grids, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨d, rfl⟩, ⟨e, he⟩⟩
    exact ⟨(d.1, e.1), (vArray_eq_grid hn d e he).symm⟩
  · rintro ⟨⟨r, s⟩, rfl⟩
    refine ⟨⟨⟨r, fun _ => s⟩, rfl⟩, ⟨⟨s, fun _ => r⟩, ?_⟩⟩
    exact (grid_transpose s r).symm

private def choiceEquiv {n : ℕ} (r : Fin 3) : Fin ((n + 2 - r.val) / 3) ≃ ColumnChoice n r where
  toFun k := ⟨⟨3 * k.val + r.val, by have h := k.isLt; omega⟩, by
    change (3 * k.val + r.val) % 3 = r.val
    omega⟩
  invFun j := ⟨j.val.val / 3, by
    have h := j.val.isLt
    have hj := j.property
    omega⟩
  left_inv k := Fin.ext (by change (3 * k.val + r.val) / 3 = k.val; omega)
  right_inv j := Subtype.ext (Fin.ext (by
    have h := j.property
    change 3 * (j.val.val / 3) + r.val = j.val.val
    omega))

private def S (n : ℕ) : ℕ := ∑ r : Fin 3, 3 ^ ((n + 2 - r.val) / 3)

private theorem data_card (n : ℕ) : Nat.card (Data n) = S n := by
  unfold S
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [Nat.card_fun, ← Nat.card_congr (choiceEquiv r), Nat.card_fin, Nat.card_fin]

private theorem total_count (n : ℕ) (hn : 3 ≤ n) :
    Nat.card { arr : Array n // Valid arr } + 9 = 2 * S n := by
  classical
  let union := vertical n ∪ horizontal n
  have union_good (a : Array n) : Valid a ↔ a ∈ union := by
    simp only [union, Finset.mem_union, mem_vertical, mem_horizontal]
    constructor
    · exact array_cases hn a
    · rintro (⟨d, rfl⟩ | ⟨d, rfl⟩)
      · exact valid_vArray d
      · exact valid_transpose (valid_vArray d)
  have ht : Nat.card { arr : Array n // Valid arr } = union.card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight union_good), Nat.card_eq_fintype_card]
    exact Fintype.card_coe union
  have hv : (vertical n).card = S n := by
    rw [vertical, Finset.card_image_of_injective _ (vArray_injective hn), Finset.card_univ,
      ← Nat.card_eq_fintype_card, data_card]
  have hh : (horizontal n).card = S n := by
    have hi : Function.Injective (transpose ∘ (@vArray n)) := by
      intro d e h
      exact vArray_injective hn (congrArg transpose h)
    rw [horizontal, Finset.card_image_of_injective _ hi, Finset.card_univ,
      ← Nat.card_eq_fintype_card, data_card]
  have hg : (grids n).card = 9 := by
    rw [grids, Finset.card_image_of_injective _ (grid_injective hn), Finset.card_univ]
    decide
  have hadd : union.card + (vertical n ∩ horizontal n).card =
      (vertical n).card + (horizontal n).card :=
    Finset.card_union_add_card_inter (vertical n) (horizontal n)
  calc
    _ = union.card + (grids n).card := by rw [ht, hg]
    _ = _ := by rw [← inter_eq_grids n hn, hadd, hv, hh]; omega

private theorem S_formula (n : ℕ) : S n = (3 + 2 * (n % 3)) * 3 ^ (n / 3) := by
  simp only [S, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.sub_zero]
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with hr | hr | hr
  · have h₀ : (n + 2) / 3 = n / 3 := by omega
    have h₁ : (n + 2 - 1) / 3 = n / 3 := by omega
    have h₂ : (n + 2 - 2) / 3 = n / 3 := by omega
    rw [h₀, h₁, h₂, hr]
    ring
  · have h₀ : (n + 2) / 3 = n / 3 + 1 := by omega
    have h₁ : (n + 2 - 1) / 3 = n / 3 := by omega
    have h₂ : (n + 2 - 2) / 3 = n / 3 := by omega
    rw [h₀, h₁, h₂, hr, pow_succ]
    ring
  · have h₀ : (n + 2) / 3 = n / 3 + 1 := by omega
    have h₁ : (n + 2 - 1) / 3 = n / 3 + 1 := by omega
    have h₂ : (n + 2 - 2) / 3 = n / 3 := by omega
    rw [h₀, h₁, h₂, hr, pow_succ]
    ring

private theorem mul_count (n : ℕ) (hn : 3 ≤ n) :
    3 * (a n + 3) = 2 * S n := by
  have h₀ := total_count n hn
  have hpow : (3 : ℕ) ^ (n / 3) = 3 * 3 ^ (n / 3 - 1) := by
    calc
      3 ^ (n / 3) = 3 ^ (n / 3 - 1 + 1) := by congr 1; omega
      _ = _ := by rw [pow_succ, mul_comm]
  have h₁ : 2 * S n = 3 * ((6 + 4 * (n % 3)) * 3 ^ (n / 3 - 1)) := by
    rw [S_formula, hpow]
    ring
  have hdiv : 3 ∣ Nat.card { arr : Array n // Valid arr } := by
    apply (Nat.dvd_add_iff_left (by decide : 3 ∣ 9)).mpr
    rw [h₀, h₁]
    exact dvd_mul_right _ _
  unfold a
  rw [if_neg (by omega), Nat.mul_add, Nat.mul_div_cancel' hdiv]
  exact h₀

theorem closed_form (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℤ) = (6 + 4 * ((n % 3 : ℕ) : ℤ)) * 3 ^ (n / 3 - 1) - 3 := by
  have hpow : (3 : ℕ) ^ (n / 3) = 3 * 3 ^ (n / 3 - 1) := by
    calc
      3 ^ (n / 3) = 3 ^ (n / 3 - 1 + 1) := by congr 1; omega
      _ = _ := by rw [pow_succ, mul_comm]
  have hc := mul_count n hn
  rw [S_formula, hpow] at hc
  have hc' : a n + 3 = (6 + 4 * (n % 3)) * 3 ^ (n / 3 - 1) := by
    have h : 3 * (a n + 3) = 3 * ((6 + 4 * (n % 3)) * 3 ^ (n / 3 - 1)) := by
      calc
        3 * (a n + 3) = _ := hc
        _ = _ := by ring
    omega
  have hz : (a n : ℤ) + 3 = (6 + 4 * ((n % 3 : ℕ) : ℤ)) * 3 ^ (n / 3 - 1) := by
    exact_mod_cast hc'
  omega

theorem recurrence (n : ℕ) (hn : 3 ≤ n) : a (n + 3) = 3 * a n + 6 := by
  have h₀ := mul_count n hn
  have h₁ := mul_count (n + 3) (by omega)
  have hs : S (n + 3) = 3 * S n := by
    rw [S_formula, S_formula]
    have hm : (n + 3) % 3 = n % 3 := by omega
    have hd : (n + 3) / 3 = n / 3 + 1 := by omega
    rw [hm, hd, pow_succ]
    ring
  omega

theorem a0 : a 0 = 0 := rfl

theorem a1 : a 1 = 0 := rfl

theorem a2 : a 2 = 0 := rfl

theorem a3 : a 3 = 3 := by
  have h := closed_form 3 (by decide)
  norm_num at h
  omega

theorem a4 : a 4 = 7 := by
  have h := closed_form 4 (by decide)
  norm_num at h
  omega

theorem a5 : a 5 = 11 := by
  have h := closed_form 5 (by decide)
  norm_num at h
  omega

end A145052Proof

namespace A145052Series

open OMA.S_oeis_a145052 PowerSeries

theorem series (h3 : a 3 = 3) (h4 : a 4 = 7) (h5 : a 5 = 11)
    (h : ∀ n : ℕ, 3 ≤ n → a (n + 3) = 3 * a n + 6) :
    (1 - X - 3 * X ^ 3 + 3 * X ^ 4) * PowerSeries.mk (fun n => (a n : ℤ)) =
      (X ^ 3 * (3 + 4 * X + 4 * X ^ 2 - 5 * X ^ 3) : ℤ⟦X⟧) := by
  have hden : (1 - X - 3 * X ^ 3 + 3 * X ^ 4 : ℤ⟦X⟧) =
      1 - X ^ 1 - C 3 * X ^ 3 + C 3 * X ^ 4 := by norm_num
  have hnum : (X ^ 3 * (3 + 4 * X + 4 * X ^ 2 - 5 * X ^ 3) : ℤ⟦X⟧) =
      C 3 * X ^ 3 + C 4 * X ^ 4 + C 4 * X ^ 5 - C 5 * X ^ 6 := by norm_num; ring
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases hn : n < 7
  · have h0 : a 0 = 0 := by simp [a]
    have h1 : a 1 = 0 := by simp [a]
    have h2 : a 2 = 0 := by simp [a]
    have h6 : a 6 = 15 := by simpa [h3] using h 3 (by omega)
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5, h6]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  simp only [if_pos (show 1 ≤ k + 7 by omega), if_pos (show 3 ≤ k + 7 by omega),
    if_pos (show 4 ≤ k + 7 by omega), if_neg (show k + 7 ≠ 3 by omega),
    if_neg (show k + 7 ≠ 4 by omega), if_neg (show k + 7 ≠ 5 by omega),
    if_neg (show k + 7 ≠ 6 by omega)]
  change (a (k + 7) : ℤ) - a (k + 6) - 3 * a (k + 4) + 3 * a (k + 3) = _
  have h7 := h (k + 4) (by omega)
  have h6 := h (k + 3) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h7 h6
  omega

end A145052Series

theorem OMA.solution : type_of% @OMA.S_oeis_a145052.main :=
  ⟨A145052Series.series A145052Proof.a3 A145052Proof.a4 A145052Proof.a5 A145052Proof.recurrence,
    A145052Proof.closed_form⟩
