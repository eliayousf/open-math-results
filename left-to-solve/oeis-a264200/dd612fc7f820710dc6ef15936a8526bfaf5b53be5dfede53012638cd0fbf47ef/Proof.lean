import OMAStatements.S_oeis_a264200
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OpenMath.RationalSetSums

open Matrix
open OMA.S_oeis_a264200 (scale values sumVal a)

def below (b : ℤ) (n : ℕ) (k : ℤ) :=
  (values b n).filter (fun x => x < k * scale b n)

def sizeVal (b : ℤ) (n : ℕ) : ℤ := scale b n * (values b n).length

def lowSum (b : ℤ) (n : ℕ) (k : ℤ) := (below b n k).sum

def lowSize (b : ℤ) (n : ℕ) (k : ℤ) : ℤ := scale b n * (below b n k).length

private theorem scale_step (b : ℤ) (n : ℕ) :
    scale b (n + 1) = b * scale b n := by simp [scale, pow_succ']

private theorem scale_pos {b : ℤ} (hb : 0 < b) (n : ℕ) : 0 < scale b n :=
  pow_pos hb n

private theorem value_pos {b : ℤ} (hb : 0 < b) (n : ℕ) {x : ℤ} (hx : x ∈ values b n) : 0 < x := by
  induction n generalizing x with
  | zero =>
    simp [values] at hx
    omega
  | succ n ih =>
    rw [values, List.mem_append] at hx
    rcases hx with hshift | hdiv
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hshift
      exact mul_pos hb (add_pos (ih hy) (scale_pos hb n))
    · exact ih (List.mem_filter.mp hdiv).1

private theorem below_zero {b : ℤ} (hb : 0 < b) (n : ℕ) :
    below b n 0 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨ht, hxlt⟩ := List.mem_filter.mp hx
  have hp := value_pos hb n ht
  simp at hxlt
  omega

private theorem below_step {b k : ℤ} (hb : 0 < b) (hk : 1 ≤ k) (n : ℕ) :
    below b (n + 1) k = (below b n (k - 1)).map (fun x => b * (x + scale b n)) ++
      below b n b := by
  have hs := scale_pos hb n
  unfold below
  rw [values, scale_step, List.filter_append, List.filter_map, List.filter_filter]
  congr 1
  · congr 1
    apply List.filter_congr
    intro x _
    simp only [Function.comp_apply, decide_eq_decide]
    rw [show k * (b * scale b n) = b * (k * scale b n) by ring, mul_lt_mul_iff_right₀ hb]
    constructor <;> intro h <;> nlinarith only [h]
  · apply List.filter_congr
    intro x _
    by_cases hx : x < b * scale b n
    · have hmul := mul_nonneg (show 0 ≤ k - 1 by omega) (mul_pos hb hs).le
      have hx' : x < k * (b * scale b n) :=
        hx.trans_le (by nlinarith only [hmul])
      simp [hx, hx']
    · simp [hx]

private theorem sum_shift (l : List ℤ) (b d : ℤ) :
    (l.map (fun x => b * (x + d))).sum = b * l.sum + b * d * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ, ih]; ring

private theorem totals_step (b : ℤ) (n : ℕ) :
    sumVal b (n + 1) = b * sumVal b n + b * sizeVal b n + lowSum b n b ∧
    sizeVal b (n + 1) = b * sizeVal b n + b * lowSize b n b := by
  simp only [sumVal, sizeVal, lowSum, lowSize, below, values, List.sum_append,
    List.length_append, Nat.cast_add, List.length_map, sum_shift, scale_step]
  constructor <;> ring

private theorem lows_step {b k : ℤ} (hb : 0 < b) (hk : 1 ≤ k) (n : ℕ) :
    lowSum b (n + 1) k = b * lowSum b n (k-1) + b * lowSize b n (k-1) + lowSum b n b ∧
    lowSize b (n + 1) k = b * lowSize b n (k-1) + b * lowSize b n b := by
  simp only [lowSum, lowSize, below_step hb hk, List.sum_append, List.length_append,
    Nat.cast_add, List.length_map, sum_shift, scale_step]
  constructor <;> ring


private def state2 (n : ℕ) : Fin 6 → ℤ :=
  ![sumVal 2 n, sizeVal 2 n, lowSum 2 n 1, lowSum 2 n 2, lowSize 2 n 1, lowSize 2 n 2]

private def matrix2 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, 2, 0, 1, 0, 0;
    0, 2, 0, 0, 0, 2;
    0, 0, 0, 1, 0, 0;
    0, 0, 2, 1, 2, 0;
    0, 0, 0, 0, 0, 2;
    0, 0, 0, 0, 2, 2]

private theorem state2_step (n : ℕ) : state2 (n + 1) = matrix2 *ᵥ state2 n := by
  obtain ⟨hS, hC⟩ := totals_step 2 n
  have hzero := below_zero (b := 2) (by decide) n
  have hzS : lowSum 2 n 0 = 0 := by simp [lowSum, hzero]
  have hzC : lowSize 2 n 0 = 0 := by simp [lowSize, hzero]
  have h1 := lows_step (b := 2) (k := 1) (by decide) (by decide) n
  have h2 := lows_step (b := 2) (k := 2) (by decide) (by decide) n
  norm_num [hzS, hzC] at h1 h2
  funext i
  fin_cases i <;> simp [state2, matrix2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals
    first
    | exact hS
    | linarith only [hS, hC, h1.1, h1.2, h2.1, h2.2]

private theorem state2_recurrence (n : ℕ) :
    state2 (n + 4) = (3 : ℤ) • state2 (n + 3) + (4 : ℤ) • state2 (n + 2) - (8 : ℤ) • state2 (n + 1) - (8 : ℤ) • state2 n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := congrArg (fun v => matrix2 *ᵥ v) ih
    simpa only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, ← state2_step,
      Nat.add_assoc, Nat.add_comm 1, Nat.reduceAdd] using h

private def state3 (n : ℕ) : Fin 8 → ℤ :=
  ![sumVal 3 n, sizeVal 3 n, lowSum 3 n 1, lowSum 3 n 2, lowSum 3 n 3, lowSize 3 n 1, lowSize 3 n 2, lowSize 3 n 3]

private def matrix3 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![3, 3, 0, 0, 1, 0, 0, 0;
    0, 3, 0, 0, 0, 0, 0, 3;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 3, 0, 1, 3, 0, 0;
    0, 0, 0, 3, 1, 0, 3, 0;
    0, 0, 0, 0, 0, 0, 0, 3;
    0, 0, 0, 0, 0, 3, 0, 3;
    0, 0, 0, 0, 0, 0, 3, 3]

private theorem state3_step (n : ℕ) : state3 (n + 1) = matrix3 *ᵥ state3 n := by
  obtain ⟨hS, hC⟩ := totals_step 3 n
  have hzero := below_zero (b := 3) (by decide) n
  have hzS : lowSum 3 n 0 = 0 := by simp [lowSum, hzero]
  have hzC : lowSize 3 n 0 = 0 := by simp [lowSize, hzero]
  have h1 := lows_step (b := 3) (k := 1) (by decide) (by decide) n
  have h2 := lows_step (b := 3) (k := 2) (by decide) (by decide) n
  have h3 := lows_step (b := 3) (k := 3) (by decide) (by decide) n
  norm_num [hzS, hzC] at h1 h2 h3
  funext i
  fin_cases i <;> simp [state3, matrix3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals
    first
    | exact hS
    | linarith only [hS, hC, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

private theorem state3_recurrence (n : ℕ) :
    state3 (n + 6) = (4 : ℤ) • state3 (n + 5) + (9 : ℤ) • state3 (n + 4) + (18 : ℤ) • state3 (n + 3) - (81 : ℤ) • state3 (n + 2) - (162 : ℤ) • state3 (n + 1) - (243 : ℤ) • state3 n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := congrArg (fun v => matrix3 *ᵥ v) ih
    simpa only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, ← state3_step,
      Nat.add_assoc, Nat.add_comm 1, Nat.reduceAdd] using h

theorem conjecture2 (n : ℕ) (hn : 4 ≤ n) :
    a 2 n = 3 * a 2 (n - 1) + 4 * a 2 (n - 2) - 8 * a 2 (n - 3) - 8 * a 2 (n - 4) := by
  by_cases he : n = 4
  · subst n
    decide
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = (k + 3) + 1 by omega,
    show k + 5 - 2 = (k + 2) + 1 by omega,
    show k + 5 - 3 = (k + 1) + 1 by omega,
    show k + 5 - 4 = k + 1 by omega]
  change sumVal 2 (k + 4) = 3 * sumVal 2 (k + 3) + 4 * sumVal 2 (k + 2) - 8 * sumVal 2 (k + 1) - 8 * sumVal 2 k
  have h := congrFun (state2_recurrence k) (0 : Fin 6)
  exact h

theorem conjecture3 (n : ℕ) (hn : 6 ≤ n) :
    a 3 n = 4 * a 3 (n - 1) + 9 * a 3 (n - 2) + 18 * a 3 (n - 3) - 81 * a 3 (n - 4) - 162 * a 3 (n - 5) - 243 * a 3 (n - 6) := by
  by_cases he : n = 6
  · subst n
    decide
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  simp only [show k + 7 - 1 = (k + 5) + 1 by omega,
    show k + 7 - 2 = (k + 4) + 1 by omega,
    show k + 7 - 3 = (k + 3) + 1 by omega,
    show k + 7 - 4 = (k + 2) + 1 by omega,
    show k + 7 - 5 = (k + 1) + 1 by omega,
    show k + 7 - 6 = k + 1 by omega]
  change sumVal 3 (k + 6) = 4 * sumVal 3 (k + 5) + 9 * sumVal 3 (k + 4) + 18 * sumVal 3 (k + 3) - 81 * sumVal 3 (k + 2) - 162 * sumVal 3 (k + 1) - 243 * sumVal 3 k
  have h := congrFun (state3_recurrence k) (0 : Fin 8)
  exact h

end OpenMath.RationalSetSums

theorem OMA.solution : type_of% @OMA.S_oeis_a264200.main := by
  exact OpenMath.RationalSetSums.conjecture2
