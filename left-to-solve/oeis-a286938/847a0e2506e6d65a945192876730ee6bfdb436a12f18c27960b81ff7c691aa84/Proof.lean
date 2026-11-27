import OMAStatements.S_oeis_a286938
import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace OpenMath.A286938

open Matrix

open OMA.S_oeis_a286938 (rewriteWord word a)

private def splitGap (r : Fin 4) : List (Fin 4) := ![[1],[2],[3,0],[3,1]] r
private def tailGap (t : Fin 3) : List (Fin 4) := ![[],[],[3]] t
private def nextTail (t : Fin 3) : Fin 3 := ![1,2,0] t

private def body (tail : Fin 3) : List (Fin 4) → List Bool
  | [] => List.replicate tail.val false
  | r :: rs => List.replicate r.val false ++ (true :: body tail rs)

private def gaps : ℕ → List (Fin 4) × Fin 3
  | 0 => ([],0)
  | n + 1 =>
      let (rs,t) := gaps n
      (0 :: (rs.flatMap splitGap ++ tailGap t), nextTail t)

private theorem body_append (t : Fin 3) (rs ys : List (Fin 4)) :
    body t (rs ++ ys) = rs.flatMap (fun r => List.replicate r.val false ++ [true]) ++ body t ys := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [body, ih, List.append_assoc]

private theorem step_body (t : Fin 3) (rs : List (Fin 4)) :
    false :: rewriteWord (body t rs) =
      body (nextTail t) (rs.flatMap splitGap ++ tailGap t) := by
  induction rs with
  | nil => fin_cases t <;> rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    rw [body_append]
    rw [← ih]
    fin_cases r <;> rfl

private theorem word_eq (n : ℕ) :
    word (n + 1) = false :: false :: true :: body (gaps n).2 (gaps n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n + 1 + 1 = (n + 1) + 1 by rfl, word, ih, gaps]
    change false :: false :: true :: true :: false :: rewriteWord (body (gaps n).2 (gaps n).1) = _
    rw [step_body]
    rfl


private def count (r : Fin 4) (rs : List (Fin 4)) : ℤ := rs.count r
private def flag (k t : Fin 3) : ℤ := if t = k then 1 else 0

private theorem count_split (rs : List (Fin 4)) :
    count 0 (rs.flatMap splitGap) = count 2 rs ∧
    count 1 (rs.flatMap splitGap) = count 0 rs + count 3 rs ∧
    count 2 (rs.flatMap splitGap) = count 1 rs ∧
    count 3 (rs.flatMap splitGap) = count 2 rs + count 3 rs := by
  induction rs with
  | nil => decide
  | cons r rs ih =>
    rcases ih with ⟨h0, h1, h2, h3⟩
    fin_cases r <;>
      simp [count, splitGap] at h0 h1 h2 h3 ⊢ <;> omega

private theorem length_body (t : Fin 3) (rs : List (Fin 4)) :
    ((body t rs).length : ℤ) = count 0 rs + 2 * count 1 rs +
      3 * count 2 rs + 4 * count 3 rs + flag 1 t + 2 * flag 2 t := by
  induction rs with
  | nil => fin_cases t <;> decide
  | cons r rs ih =>
    fin_cases r <;> simp [body, count] at ih ⊢ <;> omega

private def matrix : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1,0,0,0,0,0,0,0;
     1,0,0,1,0,0,0,0;
     0,1,0,0,1,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,1,0,0,1;
     0,0,0,0,0,0,0,1;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,1,0]

private def stats (rs : List (Fin 4)) (t : Fin 3) : Fin 8 → ℤ :=
  ![1, count 0 rs, count 1 rs, count 2 rs, count 3 rs, flag 0 t, flag 1 t, flag 2 t]

private def state (n : ℕ) : Fin 8 → ℤ :=
  stats (gaps n).1 (gaps n).2

private theorem state_step (n : ℕ) : state (n + 1) = matrix *ᵥ state n := by
  rcases he : gaps n with ⟨rs,t⟩
  simp only [state, gaps, he]
  have ⟨h0,h1,h2,h3⟩ := count_split rs
  funext i
  fin_cases i <;> fin_cases t <;>
    simp [stats, matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, tailGap,
      nextTail, flag, count] at h0 h1 h2 h3 ⊢ <;> omega

private def weight : ℕ → Fin 8 → ℤ
  | 0 => ![3,1,2,3,4,0,1,2]
  | k + 1 => weight k ᵥ* matrix

private theorem length_state (n : ℕ) : (a (n + 1) : ℤ) = weight 0 ⬝ᵥ state n := by
  rw [a, word_eq]
  simp [weight, state, stats, dotProduct, Fin.sum_univ_succ, Nat.cast_succ]
  have h := length_body (gaps n).2 (gaps n).1
  omega

private theorem weighted (n k : ℕ) : (a (n+k+1) : ℤ) = weight k ⬝ᵥ state n := by
  induction k generalizing n with
  | zero => simpa using length_state n
  | succ k ih =>
    have h := ih (n+1)
    rw [state_step, dotProduct_mulVec, ← weight] at h
    simpa only [show n + 1 + k + 1 = n + (k + 1) + 1 by omega] using h

set_option maxHeartbeats 4000000 in
private theorem weight_identity :
    weight 5 = (2:ℤ) • weight 4 - weight 3 + (2:ℤ) • weight 2 - (3:ℤ) • weight 1 + weight 0 := by
  decide

theorem main (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℤ) = 2 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ) + 2 * (a (n - 3) : ℤ) -
      3 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ) := by
  by_cases he : n = 5
  · subst n
    decide
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  simp only [show k + 6 = k+5+1 by omega, show k + 5 + 1 - 1 = k+4+1 by omega,
    show k + 5 + 1 - 2 = k+3+1 by omega, show k + 5 + 1 - 3 = k+2+1 by omega,
    show k + 5 + 1 - 4 = k+1+1 by omega, show k + 5 + 1 - 5 = k+0+1 by omega]
  rw [weighted k 5, weighted k 4, weighted k 3, weighted k 2, weighted k 1, weighted k 0, weight_identity]
  simp only [add_dotProduct, sub_dotProduct, smul_dotProduct]
  rfl

end OpenMath.A286938

theorem OMA.solution : type_of% @OMA.S_oeis_a286938.main := by
  exact OpenMath.A286938.main
