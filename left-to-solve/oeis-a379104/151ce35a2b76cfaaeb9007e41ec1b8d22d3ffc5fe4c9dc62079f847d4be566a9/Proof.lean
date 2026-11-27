import OMAStatements.S_oeis_a379104
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

/-! Common recurrences for the elementary symmetric sums of Fibonacci and Lucas prefixes. -/

namespace A379104Proof

open scoped BigOperators Polynomial
open Finset Polynomial Matrix OMA.S_oeis_a379104

private theorem elementary_zero (u : ℕ → ℤ) (n : ℕ) : elementary u 0 n = 1 := by
  simp [elementary, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]

private theorem elementary_succ (u : ℕ → ℤ) (j n : ℕ) :
    elementary u (j + 1) (n + 1) = elementary u (j + 1) n + u n * elementary u j n := by
  simp only [elementary, prod_range_succ, mul_add, mul_one, coeff_add, ← mul_assoc,
    coeff_mul_X, coeff_mul_C, mul_comm (u n)]

private abbrev Index (k : ℕ) := Σ r : Fin (k + 1), Fin (r.val + 1)

private noncomputable def state (u : ℕ → ℤ) (k n : ℕ) (v : Index k) : ℤ :=
  elementary u (k - v.1.val) n * u n ^ v.2.val * u (n + 1) ^ (v.1.val - v.2.val)

private def T (k : ℕ) : Matrix (Index k) (Index k) ℤ := fun v w =>
  (if w.1 = v.1 then ((v.1.val - v.2.val).choose w.2.val : ℤ) else 0) +
    (if w.1.val = v.1.val + 1 ∧ 0 < w.2.val then
      ((v.1.val - v.2.val).choose (w.2.val - 1) : ℤ) else 0)

private theorem binomial_sum (x y : ℤ) {r i : ℕ} (hi : i ≤ r) :
    (∑ j ∈ range (r + 1), ((r - i).choose j : ℤ) * x ^ j * y ^ (r - j)) =
      y ^ i * (x + y) ^ (r - i) := by
  rw [add_pow, mul_sum]
  rw [← sum_subset (range_mono (show r - i + 1 ≤ r + 1 by omega))]
  · apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [show r - j = i + (r - i - j) by omega, pow_add]
    ring
  · intro j _ hj
    rw [Nat.choose_eq_zero_of_lt (by simp only [mem_range] at hj; omega)]
    simp

private theorem binomial_succ_sum (x y : ℤ) {r i : ℕ} (hi : i ≤ r) :
    (∑ j ∈ range (r + 2), (if 0 < j then ((r - i).choose (j - 1) : ℤ) else 0) *
        x ^ j * y ^ (r + 1 - j)) = x * (y ^ i * (x + y) ^ (r - i)) := by
  rw [sum_range_succ']
  simp only [Nat.zero_lt_succ, if_true, Nat.add_sub_cancel, add_tsub_add_eq_tsub_right,
    lt_self_iff_false, if_false, zero_mul, add_zero, pow_succ]
  rw [← binomial_sum x y hi, mul_sum]
  apply sum_congr rfl
  intro j _
  ring

private theorem card_index (k : ℕ) : Fintype.card (Index k) = (k + 1) * (k + 2) / 2 := by
  have h : (∑ r ∈ range (k + 2), r) = ∑ r ∈ range (k + 1), (r + 1) := by
    rw [sum_range_succ']
    simp
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have e : (∑ r : Fin (k + 1), (r.val + 1)) = ∑ r ∈ range (k + 1), (r + 1) :=
    Fin.sum_univ_eq_sum_range (fun r => r + 1) (k + 1)
  rw [e, ← h, sum_range_id]
  rw [show k + 2 - 1 = k + 1 by omega, Nat.mul_comm]

private theorem state_step (u : ℕ → ℤ) (hu : ∀ n, u (n + 2) = u n + u (n + 1))
    (k n : ℕ) : T k *ᵥ state u k n = state u k (n + 1) := by
  ext v
  rcases v with ⟨r, i⟩
  have hi : i.val ≤ r.val := by have := i.isLt; omega
  let x := u n
  let y := u (n + 1)
  let factor := y ^ i.val * (x + y) ^ (r.val - i.val)
  unfold Matrix.mulVec dotProduct T
  simp only [add_mul, sum_add_distrib, Fintype.sum_sigma]
  have hsame :
      (∑ s : Fin (k + 1), ∑ j : Fin (s.val + 1),
        (if s = r then ((r.val - i.val).choose j.val : ℤ) else 0) * state u k n ⟨s,j⟩) =
      elementary u (k - r.val) n * factor := by
    rw [Finset.sum_eq_single r]
    · simp only [state, if_true]
      rw [Fin.sum_univ_eq_sum_range (fun j => ((r.val - i.val).choose j : ℤ) *
        (elementary u (k - r.val) n * u n ^ j * u (n + 1) ^ (r.val - j)))]
      unfold factor
      rw [← binomial_sum x y hi, mul_sum]
      apply sum_congr rfl
      intro j _
      dsimp [x,y]
      ring
    · intro s _ hs
      simp [hs]
    · simp
  rw [hsame]
  by_cases hr : r.val < k
  · let next : Fin (k+1) := ⟨r.val+1, by omega⟩
    have hnext :
        (∑ s : Fin (k + 1), ∑ j : Fin (s.val + 1),
          (if s.val = r.val + 1 ∧ 0 < j.val then
              ((r.val - i.val).choose (j.val - 1) : ℤ) else 0) * state u k n ⟨s,j⟩) =
        elementary u (k - (r.val + 1)) n * (x * factor) := by
      rw [Finset.sum_eq_single next]
      · simp only [state, next, true_and]
        rw [Fin.sum_univ_eq_sum_range (fun j =>
          (if 0 < j then ((r.val - i.val).choose (j - 1) : ℤ) else 0) *
            (elementary u (k - (r.val + 1)) n * u n ^ j * u (n + 1) ^ (r.val + 1 - j)))]
        unfold factor
        rw [← binomial_succ_sum x y hi, mul_sum]
        apply sum_congr rfl
        intro j _
        dsimp [x,y]
        ring
      · intro s _ hs
        have hneq : s.val ≠ r.val + 1 := fun h => hs (Fin.ext h)
        simp [hneq]
      · simp
    rw [hnext]
    have he : elementary u (k-r.val) (n+1) =
        elementary u (k-r.val) n + u n * elementary u (k-(r.val+1)) n := by
      have hj : k - (r.val + 1) + 1 = k - r.val := by omega
      simpa only [hj] using elementary_succ u (k - (r.val + 1)) n
    simp only [state, hu, he]
    dsimp [x,y,factor]
    ring
  · have htop : r.val = k := by have := r.isLt; omega
    have hnext :
        (∑ s : Fin (k + 1), ∑ j : Fin (s.val + 1),
          (if s.val = r.val + 1 ∧ 0 < j.val then
              ((r.val - i.val).choose (j.val - 1) : ℤ) else 0) * state u k n ⟨s,j⟩) = 0 := by
      apply sum_eq_zero
      intro s _
      have hneq : s.val ≠ r.val + 1 := by have := s.isLt; omega
      simp [hneq]
    rw [hnext, add_zero]
    simp [state, hu, factor, x,y, htop, elementary_zero]

private def diagonalBlock (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ :=
  fun i j => ((r - i.val).choose j.val : ℤ)

private theorem diagonalBlock_det_ne_zero (r : ℕ) : (diagonalBlock r).det ≠ 0 := by
  let reversed := (diagonalBlock r).submatrix id Fin.revPerm
  have htri : reversed.IsUpperTriangular := by
    intro i j hj
    change ((r - i.val).choose ((r + 1) - (j.val + 1)) : ℤ) = 0
    have hi := i.isLt
    change j.val < i.val at hj
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    rfl
  have hdiag (i : Fin (r + 1)) : reversed i i = 1 := by
    change ((r - i.val).choose ((r + 1) - (i.val + 1)) : ℤ) = 1
    rw [show (r + 1) - (i.val + 1) = r - i.val by omega, Nat.choose_self]
    rfl
  have hdet : reversed.det = 1 := by rw [det_of_isUpperTriangular htri]; simp [hdiag]
  intro hz
  have hreversed := Matrix.det_permute' Fin.revPerm (diagonalBlock r)
  change reversed.det = _ at hreversed
  simp [hdet, hz] at hreversed

private def blockIndex (k : ℕ) (r : Fin (k + 1)) :
    Fin (r.val + 1) ≃ {v : Index k // v.1 = r} where
  toFun j := ⟨⟨r, j⟩, rfl⟩
  invFun := fun ⟨⟨s, j⟩, h⟩ => by
    change s = r at h
    subst s
    exact j
  left_inv := fun j => rfl
  right_inv := by
    rintro ⟨⟨s, j⟩, h⟩
    change s = r at h
    subst s
    rfl

private theorem transition_det_ne_zero (k : ℕ) : (T k).det ≠ 0 := by
  classical
  let degree : Index k → Fin (k + 1) := Sigma.fst
  have htri : (T k).BlockTriangular degree := by
    intro v w h
    change w.1 < v.1 at h
    have hne : w.1.val ≠ v.1.val + 1 := by
      change w.1.val < v.1.val at h
      omega
    simp [T, ne_of_lt h, hne]
  rw [htri.det_fintype]
  refine Finset.prod_ne_zero_iff.mpr fun r _ => ?_
  let e : Fin (r.val + 1) ≃ {v : Index k // degree v = r} := blockIndex k r
  rw [← Matrix.det_submatrix_equiv_self e]
  have hblock : ((T k).toSquareBlock degree r).submatrix e e = diagonalBlock r.val := by
    ext i j
    change (T k) ⟨r, i⟩ ⟨r, j⟩ = diagonalBlock r.val i j
    simp [T, diagonalBlock]
  rw [hblock]
  exact diagonalBlock_det_ne_zero r.val

private theorem pow_mulVec_state (u : ℕ → ℤ)
    (hu : ∀ n, u (n + 2) = u n + u (n + 1)) (k n i : ℕ) :
    T k ^ i *ᵥ state u k n = state u k (n + i) := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, state_step u hu, Nat.add_assoc]

private theorem recurrence (u : ℕ → ℤ) (hu : ∀ n, u (n + 2) = u n + u (n + 1))
    (k : ℕ) : IsRecurrence (T k).charpoly u k := by
  intro n
  have h := Matrix.aeval_self_charpoly (T k)
  rw [Polynomial.aeval_eq_sum_range] at h
  have hv := congrArg (fun m : Matrix (Index k) (Index k) ℤ => m *ᵥ state u k n) h
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.zero_mulVec,
    pow_mulVec_state u hu] at hv
  let first : Index k := ⟨⟨0, Nat.zero_lt_succ k⟩, ⟨0, Nat.zero_lt_succ 0⟩⟩
  have hfirst := congrArg (fun v : Index k → ℤ => v first) hv
  simpa [first, state, Finset.sum_apply, smul_eq_mul] using hfirst

/-- One integer recurrence of the stated order works for both prefixes. -/
theorem main (k : ℕ) (_hk : 1 ≤ k) :
    ∃ p : ℤ[X], p.Monic ∧ p.natDegree = (k + 1) * (k + 2) / 2 ∧ p.coeff 0 ≠ 0 ∧
      IsRecurrence p a k ∧ IsRecurrence p b k := by
  refine ⟨(T k).charpoly, Matrix.charpoly_monic _, ?_, ?_,
    recurrence a (fun _ => rfl) k, recurrence b (fun _ => rfl) k⟩
  · rw [Matrix.charpoly_natDegree_eq_dim, card_index]
  · intro hz
    apply transition_det_ne_zero k
    rw [Matrix.det_eq_sign_charpoly_coeff, hz, mul_zero]

end A379104Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a379104.main := A379104Proof.main
