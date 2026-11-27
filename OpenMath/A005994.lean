import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith

/-! Mathar's OEIS A005994 identity with the zero-sum array count A203286. -/

open Finset

namespace OpenMath.A005994

/-- The multiplicities of the magnitudes one, two, and three. -/
@[ext] structure Counts where
  one : ℕ
  two : ℕ
  three : ℕ

private def total (t : Counts) : ℕ := t.one + t.two + t.three

private def weight (t : Counts) : ℕ := t.one + 2 * t.two + 3 * t.three

/-- Positive and negative multiplicities of a nondecreasing array of length `2*n`.
The other `2*(n-total p.1)` entries are zeros. -/
def Configuration (n : ℕ) :=
  {p : Counts × Counts // total p.1 = total p.2 ∧ weight p.1 = weight p.2 ∧ total p.1 ≤ n}

private def Core (n : ℕ) := {t : Counts // total t ≤ n}

private abbrev Three (n : ℕ) :=
  Σ a : Fin (n + 1), Σ b : Fin (n - a + 1), Fin (n - a - b + 1)

private def coreEquiv (n : ℕ) : Core n ≃ Three n where
  toFun := fun ⟨⟨a,b,c⟩,h⟩ => by
    change a + b + c ≤ n at h
    exact ⟨⟨a, by omega⟩, ⟨b, by change b < n - a + 1; omega⟩,
      ⟨c, by change c < n - a - b + 1; omega⟩⟩
  invFun := fun ⟨a,b,c⟩ => by
    refine ⟨⟨a,b,c⟩, ?_⟩
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    change (a : ℕ) + (b : ℕ) + (c : ℕ) ≤ n
    omega
  left_inv := fun ⟨⟨_,_,_⟩,_⟩ => rfl
  right_inv := fun ⟨⟨_,_⟩,⟨_,_⟩,⟨_,_⟩⟩ => rfl

private theorem sum_diag (n k : ℕ) :
    (∑ j ∈ range (n+1), (j+k).choose k) = (n+k+1).choose (k+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n.succ + 1 = n + 1 + 1 by omega, sum_range_succ, ih,
      show n + 1 + k = n + k + 1 by omega]
    exact (Nat.add_comm _ _).trans (Nat.choose_succ_succ' (n + k + 1) k).symm

private theorem sum_diag_reflect (n k : ℕ) :
    (∑ j ∈ range (n+1), (n-j+k).choose k) = (n+k+1).choose (k+1) := by
  simpa only [Nat.add_sub_cancel] using
    (sum_range_reflect (fun j => (j+k).choose k) (n+1)).trans (sum_diag n k)

private noncomputable instance coreFintype (n : ℕ) : Fintype (Core n) :=
  Fintype.ofEquiv (Three n) (coreEquiv n).symm

private theorem core_card (n : ℕ) : Fintype.card (Core n) = (n+3).choose 3 := by
  rw [Fintype.card_congr (coreEquiv n)]
  change Fintype.card (Σ a : Fin (n + 1), Σ b : Fin (n-a+1), Fin (n-a-b+1)) = _
  simp only [Fintype.card_sigma, Fintype.card_fin]
  have h (a : Fin (n+1)) :
      (∑ b : Fin (n-a+1), (n-a-b+1)) = (n-a+2).choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun b : ℕ => n - a - b + 1)]
    simpa only [Nat.choose_one_right] using sum_diag_reflect (n-a) 1
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => (n - a + 2).choose 2)]
  exact sum_diag_reflect n 2

/-- `none` is the equal-multiplicity case. Otherwise the magnitude is one plus
the index, and the Boolean is the orientation. -/
private abbrev Mode (n : ℕ) := Option (Bool × Fin (n / 2))

private def shift {n : ℕ} : Mode n → ℕ
  | none => 0
  | some (_, j) => (j : ℕ) + 1

private def signedShift {n : ℕ} : Mode n → ℤ
  | none => 0
  | some (false, j) => -((j : ℤ) + 1)
  | some (true, j) => (j : ℤ) + 1

private def addOuter (t : Counts) (d : ℕ) : Counts := ⟨t.one+d, t.two, t.three+d⟩

private def addMiddle (t : Counts) (d : ℕ) : Counts := ⟨t.one, t.two+2*d, t.three⟩

private abbrev Normal (n : ℕ) := Σ m : Mode n, Core (n - 2 * shift m)

private def assemble (n : ℕ) : Normal n → Configuration n
  | ⟨none, ⟨t,h⟩⟩ => ⟨(t,t), rfl, rfl, by simpa [shift] using h⟩
  | ⟨some (false,j), ⟨t,h⟩⟩ => by
    have hj := j.isLt
    exact ⟨(addMiddle t (j+1), addOuter t (j+1)), by
      simp only [addMiddle, addOuter, total, weight, shift] at h ⊢
      omega⟩
  | ⟨some (true,j), ⟨t,h⟩⟩ => by
    have hj := j.isLt
    exact ⟨(addOuter t (j+1), addMiddle t (j+1)), by
      simp only [addMiddle, addOuter, total, weight, shift] at h ⊢
      omega⟩

private theorem signedShift_injective (n : ℕ) : Function.Injective (@signedShift n) := by
  rintro (_ | ⟨a,j⟩) (_ | ⟨b,k⟩) h
  · rfl
  · cases b <;> simp [signedShift] at h <;> omega
  · cases a <;> simp [signedShift] at h <;> omega
  · cases a <;> cases b <;> simp [signedShift] at h ⊢ <;> omega

private def gap {n : ℕ} (p : Configuration n) : ℤ :=
  (p.val.1.one : ℤ) - (p.val.2.one : ℤ)

private def shared {n : ℕ} (p : Configuration n) : Counts :=
  ⟨min p.val.1.one p.val.2.one, min p.val.1.two p.val.2.two,
    min p.val.1.three p.val.2.three⟩

private theorem gap_assemble (n : ℕ) (p : Normal n) :
    gap (assemble n p) = signedShift p.fst := by
  rcases p with ⟨_ | ⟨b,j⟩, ⟨t,_⟩⟩
  · simp [gap, assemble, signedShift]
  · cases b <;> simp [gap, assemble, signedShift, addMiddle, addOuter]

private theorem shared_assemble (n : ℕ) (p : Normal n) :
    shared (assemble n p) = p.snd.val := by
  rcases p with ⟨_ | ⟨b,j⟩, ⟨⟨a,u,v⟩,_⟩⟩
  · simp [shared, assemble]
  · cases b <;> apply Counts.ext <;> simp [shared, assemble, addMiddle, addOuter]

private theorem assemble_injective (n : ℕ) : Function.Injective (assemble n) := by
  rintro ⟨m,c⟩ ⟨m',c'⟩ h
  have hm : m = m' := by
    apply signedShift_injective n
    simpa only [gap_assemble] using congrArg gap h
  subst m'
  have hc : c = c' := by
    apply Subtype.ext
    simpa only [shared_assemble] using congrArg shared h
  subst c'
  rfl

private theorem assemble_surjective (n : ℕ) : Function.Surjective (assemble n) := by
  rintro ⟨⟨⟨a,b,c⟩,⟨u,v,w⟩⟩, ht, hw, hn⟩
  simp only [total, weight] at ht hw hn
  by_cases h : a = u
  · have hb : b = v := by omega
    have hc : c = w := by omega
    subst u; subst v; subst w
    exact ⟨⟨none, ⟨⟨a,b,c⟩, by simpa [shift,total] using hn⟩⟩, rfl⟩
  · by_cases hlt : u < a
    · let j : Fin (n/2) := ⟨a-u-1, by omega⟩
      refine ⟨⟨some (true,j), ⟨⟨u,b,w⟩, by simp only [j, shift, total]; omega⟩⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext <;> apply Counts.ext <;> simp [j, assemble, addOuter, addMiddle] <;> omega
    · let j : Fin (n/2) := ⟨u-a-1, by omega⟩
      refine ⟨⟨some (false,j), ⟨⟨a,v,c⟩, by simp only [j, shift, total]; omega⟩⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext <;> apply Counts.ext <;> simp [j, assemble, addOuter, addMiddle] <;> omega

private noncomputable def configEquiv (n : ℕ) : Normal n ≃ Configuration n :=
  Equiv.ofBijective (assemble n) ⟨assemble_injective n, assemble_surjective n⟩

/-- The A203286 count, with nondecreasing arrays encoded by their multiplicities. -/
noncomputable def arrayCount (n : ℕ) : ℕ := Nat.card (Configuration n)

private def triangle (n d : ℕ) : ℕ := (n + 2 - 2 * d).choose 2

private def tetrahedron (n d : ℕ) : ℕ := (n + 3 - 2 * d).choose 3

private theorem core_nat_card (n : ℕ) : Nat.card (Core n) = (n+3).choose 3 := by
  rw [Nat.card_eq_fintype_card, core_card]

private theorem array_formula (n : ℕ) :
    arrayCount n = tetrahedron n 0 + 2 * ∑ j ∈ range (n / 2), tetrahedron n (j+1) := by
  rw [arrayCount, Nat.card_congr (configEquiv n).symm, Nat.card_sigma, Fintype.sum_option]
  simp only [core_nat_card, shift, Nat.mul_zero, Nat.sub_zero, Fintype.sum_prod_type, Fintype.sum_bool]
  have h : (∑ j : Fin (n / 2), (n - 2 * (j.val + 1) + 3).choose 3) =
      ∑ j ∈ range (n / 2), tetrahedron n (j+1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (n - 2 * (j + 1) + 3).choose 3)]
    apply sum_congr rfl
    intro j hj
    have hlt := mem_range.mp hj
    unfold tetrahedron
    congr 1
    omega
  rw [h, show tetrahedron n 0 = (n + 3).choose 3 by simp [tetrahedron]]
  omega

/-- The A005994 sequence by the OEIS triangular-number convolution. Terms beyond
`n / 2` vanish. -/
def alkaneCount (n : ℕ) : ℕ :=
  ∑ d ∈ range (n + 1), (2 * d + 1) * triangle n d

private theorem pascal_pair (n d : ℕ) :
    triangle n d + triangle (n+1) d + tetrahedron (n+1) (d+1) = tetrahedron (n+1) d := by
  unfold triangle tetrahedron
  by_cases h : 2 * d ≤ n + 2
  · let k := n + 2 - 2 * d
    change k.choose 2 + _ + _ = _
    rw [show n + 1 + 2 - 2 * d = k + 1 by dsimp [k]; omega,
      show n + 1 + 3 - 2 * (d + 1) = k by dsimp [k]; omega,
      show n + 1 + 3 - 2 * d = k + 1 + 1 by dsimp [k]; omega]
    have h₁ : (k+1+1).choose 3 = (k+1).choose 2 + (k+1).choose 3 :=
      Nat.choose_succ_succ' (k+1) 2
    have h₂ : (k+1).choose 3 = k.choose 2 + k.choose 3 := Nat.choose_succ_succ' k 2
    omega
  · rw [Nat.choose_eq_zero_of_lt (show n + 2 - 2 * d < 2 by omega),
      Nat.choose_eq_zero_of_lt (show n + 1 + 2 - 2 * d < 2 by omega),
      Nat.choose_eq_zero_of_lt (show n + 1 + 3 - 2 * (d + 1) < 3 by omega),
      Nat.choose_eq_zero_of_lt (show n + 1 + 3 - 2 * d < 3 by omega)]

private theorem weighted_telescope (f g : ℕ → ℕ) (h : ∀ i, g i + f (i+1) = f i)
    (m : ℕ) : (∑ i ∈ range m, (2*i+1) * g i) + (2*m+1) * f m =
      f 0 + 2 * ∑ i ∈ range m, f (i+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ]
    have hm := congrArg (fun v : ℕ => (2*m+1) * v) (h m)
    nlinarith only [ih, hm]

/-- Mathar's adjacent-sum identity for A005994 and A203286. -/
theorem main (n : ℕ) : alkaneCount n + alkaneCount (n+1) = arrayCount (n+1) := by
  have hpad : alkaneCount n = ∑ d ∈ range (n+2), (2*d+1) * triangle n d := by
    rw [alkaneCount, sum_range_succ (fun d => (2*d+1) * triangle n d) (n+1)]
    have hz : triangle n (n+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hz]
  have htail : (∑ j ∈ range ((n+1)/2), tetrahedron (n+1) (j+1)) =
      ∑ j ∈ range (n+2), tetrahedron (n+1) (j+1) := by
    apply sum_subset (range_mono (by omega))
    intro j _ hj
    simp only [mem_range, not_lt] at hj
    exact Nat.choose_eq_zero_of_lt (by omega)
  have hnext : alkaneCount (n+1) = ∑ d ∈ range (n+2), (2*d+1) * triangle (n+1) d := rfl
  rw [hpad, hnext, ← sum_add_distrib, array_formula, htail]
  simp_rw [← Nat.mul_add]
  have h := weighted_telescope (tetrahedron (n+1)) (fun d => triangle n d + triangle (n+1) d)
    (pascal_pair n) (n+2)
  have hz : tetrahedron (n+1) (n+2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simpa only [hz, Nat.mul_zero, Nat.add_zero] using h

end OpenMath.A005994
