import OMAStatements.S_oeis_a001752
import Mathlib.Data.Finset.Sigma

/-! Sum the two by two principal minors by the distance between their indices. -/

open Finset
open OMA.S_oeis_a001752

private theorem weight_eq (d : ℕ) :
    (d ^ 2 / 2) / 2 = ((d + 1) / 2) * (d / 2) := by
  let k := d / 2
  have hd : d = 2 * k ∨ d = 2 * k + 1 := by omega
  rcases hd with hd | hd
  · have h₁ : (d + 1) / 2 = k := by omega
    have h₂ : d ^ 2 = 4 * (k * k) := by rw [hd]; ring
    rw [h₁, show d / 2 = k by rfl, h₂]
    omega
  · have h₁ : (d + 1) / 2 = k + 1 := by omega
    have h₂ : d ^ 2 = 4 * ((k + 1) * k) + 1 := by rw [hd]; ring
    rw [h₁, show d / 2 = k by rfl, h₂]
    omega

private theorem twoMinor_value {n : ℕ} {i j : Fin n} (h : i < j) :
    (Matrix.submatrix (speziaMatrix n) (![i, j] : Fin 2 → Fin n) ![i, j]).det =
      (((j.val - i.val) ^ 2 / 2) / 2 : ℕ) := by
  have hij : i.val < j.val := h
  let d := j.val - i.val
  have hpos : (j.val : ℤ) - i.val = (d : ℤ) := by omega
  have hneg : (i.val : ℤ) - j.val + 1 = 1 - (d : ℤ) := by omega
  rw [Matrix.det_fin_two]
  change (((i.val : ℤ) - i.val + 1) / 2) * (((j.val : ℤ) - j.val + 1) / 2) -
    (((j.val : ℤ) - i.val + 1) / 2) * (((i.val : ℤ) - j.val + 1) / 2) =
      (((d ^ 2 / 2) / 2 : ℕ) : ℤ)
  rw [sub_self, sub_self, hneg, hpos, weight_eq]
  have hleft : ((d : ℤ) + 1) / 2 = (((d + 1) / 2 : ℕ) : ℤ) := by omega
  have hright : (1 - (d : ℤ)) / 2 = -((d / 2 : ℕ) : ℤ) := by omega
  rw [hleft, hright]
  push_cast
  ring

private def pairIndex {n : ℕ} (i j : Fin n) : Fin 2 → ↥({i, j} : Finset (Fin n)) :=
  ![⟨i, by simp⟩, ⟨j, by simp⟩]

private theorem pairIndex_bijective {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    Function.Bijective (pairIndex i j) := by
  constructor
  · intro k l hkl
    revert hkl
    revert l k
    simp [Fin.forall_fin_two, pairIndex, h, Ne.symm h]
  · intro k
    have hk : k.val = i ∨ k.val = j := by simpa only [mem_insert, mem_singleton] using k.property
    rcases hk with hi | hj
    · exact ⟨0, Subtype.ext hi.symm⟩
    · exact ⟨1, Subtype.ext hj.symm⟩

private theorem pairMinor_value {n : ℕ} {i j : Fin n} (h : i < j) :
    ((speziaMatrix n).submatrix (Subtype.val : ↥({i, j} : Finset (Fin n)) → Fin n)
      (Subtype.val : ↥({i, j} : Finset (Fin n)) → Fin n)).det =
      (((j.val - i.val) ^ 2 / 2) / 2 : ℕ) := by
  let e := Equiv.ofBijective _ (pairIndex_bijective (ne_of_lt h))
  rw [← Matrix.det_submatrix_equiv_self e]
  convert twoMinor_value h using 1
  congr 1
  ext k l
  revert k l
  simp [Fin.forall_fin_two, Matrix.submatrix_apply, e, pairIndex]

private def gapDomain (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Icc 1 n).sigma fun d => range (n - d)

private theorem gapBounds {n : ℕ} {x : Σ _ : ℕ, ℕ} (hx : x ∈ gapDomain n) :
    1 ≤ x.1 ∧ x.2 + x.1 < n := by
  obtain ⟨hd, hi⟩ := mem_sigma.mp hx
  obtain ⟨hd₁, hd₂⟩ := mem_Icc.mp hd
  have hi' := mem_range.mp hi
  omega

private def lowerIndex {n : ℕ} (x : Σ _ : ℕ, ℕ) (hx : x ∈ gapDomain n) : Fin n :=
  ⟨x.2, by have h := (gapBounds hx).2; omega⟩

private def upperIndex {n : ℕ} (x : Σ _ : ℕ, ℕ) (hx : x ∈ gapDomain n) : Fin n :=
  ⟨x.2 + x.1, (gapBounds hx).2⟩

private theorem indices_lt {n : ℕ} {x : Σ _ : ℕ, ℕ} (hx : x ∈ gapDomain n) :
    lowerIndex x hx < upperIndex x hx := by
  change x.2 < x.2 + x.1
  have h := (gapBounds hx).1
  omega

private def minorIndex {n : ℕ} (x : Σ _ : ℕ, ℕ) (hx : x ∈ gapDomain n) : Finset (Fin n) :=
  {lowerIndex x hx, upperIndex x hx}

private theorem minorIndex_injective {n : ℕ} {x y : Σ _ : ℕ, ℕ}
    {hx : x ∈ gapDomain n} {hy : y ∈ gapDomain n}
    (heq : minorIndex x hx = minorIndex y hy) : x = y := by
  have h₁ : lowerIndex x hx ∈ minorIndex y hy := heq ▸ (by simp [minorIndex])
  have h₂ : lowerIndex y hy ∈ minorIndex x hx := heq.symm ▸ (by simp [minorIndex])
  have h₃ : upperIndex x hx ∈ minorIndex y hy := heq ▸ (by simp [minorIndex])
  simp only [minorIndex, mem_insert, mem_singleton] at h₁ h₂ h₃
  have hlow : lowerIndex x hx = lowerIndex y hy := by
    apply le_antisymm
    · rcases h₂ with h | h
      · exact h.ge
      · exact (indices_lt hx).le.trans h.ge
    · rcases h₁ with h | h
      · exact h.ge
      · exact (indices_lt hy).le.trans h.ge
  have hupp : upperIndex x hx = upperIndex y hy := by
    rcases h₃ with h | h
    · exact False.elim ((ne_of_lt (indices_lt hx)) (hlow.trans h.symm))
    · exact h
  have hv₁ : x.2 = y.2 := congrArg Fin.val hlow
  have hv₂ : x.2 + x.1 = y.2 + y.1 := congrArg Fin.val hupp
  exact Sigma.ext (by omega) (heq_of_eq hv₁)

private theorem hasMinorIndex {n : ℕ} {i j : Fin n} (hij : i < j) :
    ∃ (x : Σ _ : ℕ, ℕ) (hx : x ∈ gapDomain n), minorIndex x hx = {i, j} := by
  have hij' : i.val < j.val := hij
  let x : Σ _ : ℕ, ℕ := ⟨j.val - i.val, i.val⟩
  have hx : x ∈ gapDomain n := by
    refine mem_sigma.mpr ⟨mem_Icc.mpr ?_, mem_range.mpr ?_⟩
    · change 1 ≤ j.val - i.val ∧ j.val - i.val ≤ n
      have h := j.isLt
      omega
    · change i.val < n - (j.val - i.val)
      have h := j.isLt
      omega
  refine ⟨x, hx, ?_⟩
  have hlow : lowerIndex x hx = i := Fin.ext rfl
  have hupp : upperIndex x hx = j := by
    apply Fin.ext
    change i.val + (j.val - i.val) = j.val
    omega
  simp [minorIndex, hlow, hupp]

private theorem sum_minors_by_gap (n : ℕ) :
    (∑ s ∈ (univ : Finset (Fin n)).powersetCard 2,
      ((speziaMatrix n).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det) =
    ∑ d ∈ Icc 1 n, ((n - d : ℕ) : ℤ) * (((d ^ 2 / 2) / 2 : ℕ) : ℤ) := by
  classical
  calc
    _ = ∑ x ∈ gapDomain n, (((x.1 ^ 2 / 2) / 2 : ℕ) : ℤ) := by
      symm
      refine Finset.sum_bij (fun x hx => minorIndex x hx) ?_ ?_ ?_ ?_
      · intro x hx
        simp [minorIndex, mem_powersetCard, (ne_of_lt (indices_lt hx))]
      · intro x hx y hy heq
        exact minorIndex_injective heq
      · intro s hs
        obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp (mem_powersetCard.mp hs).2
        rcases lt_or_gt_of_ne hij with h | h
        · exact hasMinorIndex h
        · obtain ⟨x, hx, hset⟩ := hasMinorIndex h
          exact ⟨x, hx, hset.trans (pair_comm j i)⟩
      · intro x hx
        rw [minorIndex, pairMinor_value (indices_lt hx)]
        have hgap : (upperIndex x hx).val - (lowerIndex x hx).val = x.1 := by
          change x.2 + x.1 - x.2 = x.1
          omega
        rw [hgap]
    _ = _ := by
      rw [gapDomain, Finset.sum_sigma]
      simp

private theorem sum_gaps_eq_a (n : ℕ) (hn : 2 < n) :
    (∑ d ∈ Icc 1 n, ((n - d : ℕ) : ℤ) * (((d ^ 2 / 2) / 2 : ℕ) : ℤ)) = (a (n - 3) : ℤ) := by
  unfold a
  have h₁ : n - 3 + 4 = n + 1 := by omega
  have h₂ : n - 3 + 3 = n := by omega
  rw [h₁, h₂]
  push_cast
  refine Finset.sum_subset (fun i hi => ?_) (fun i hi hnot => ?_)
  · exact mem_range.mpr (by have h := (mem_Icc.mp hi).2; omega)
  · have hin := mem_range.mp hi
    have hi0 : i = 0 := by
      by_contra h
      exact hnot (mem_Icc.mpr (by omega))
    simp [hi0]

theorem OMA.solution : type_of% @OMA.S_oeis_a001752.main := by
  intro n hn
  have h := Matrix.charpoly_coeff_eq_sum_minors (speziaMatrix n) 2 (by simpa using (show 2 ≤ n by omega))
  simp only [Fintype.card_fin, show (-1 : ℤ)^2 = 1 by decide, one_mul] at h
  rw [h, sum_minors_by_gap, sum_gaps_eq_a n hn, abs_of_nonneg (Int.natCast_nonneg _)]
