import OMAStatements.S_oeis_a269659
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace A269659Proof

open OMA.S_oeis_a269659

open scoped Classical

abbrev Word (n : ℕ) := Fin 6 → Fin (n + 1)

private def word {n : ℕ} (a b c d e f : Fin (n + 1)) : Word n := fun i =>
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | _ => f

@[simp] private theorem cast0 : (0 : Fin 5).castSucc = (0 : Fin 6) := rfl
@[simp] private theorem cast1 : (1 : Fin 5).castSucc = (1 : Fin 6) := rfl
@[simp] private theorem cast2 : (2 : Fin 5).castSucc = (2 : Fin 6) := rfl
@[simp] private theorem cast3 : (3 : Fin 5).castSucc = (3 : Fin 6) := rfl
@[simp] private theorem cast4 : (4 : Fin 5).castSucc = (4 : Fin 6) := rfl
@[simp] private theorem succ0 : (0 : Fin 5).succ = (1 : Fin 6) := rfl
@[simp] private theorem succ1 : (1 : Fin 5).succ = (2 : Fin 6) := rfl
@[simp] private theorem succ2 : (2 : Fin 5).succ = (3 : Fin 6) := rfl
@[simp] private theorem succ3 : (3 : Fin 5).succ = (4 : Fin 6) := rfl
@[simp] private theorem succ4 : (4 : Fin 5).succ = (5 : Fin 6) := rfl

private def valid {n : ℕ} (w : Word n) :=
  ∀ i j : Fin 5, i < j → ¬ repeated w i j

private def triple {n : ℕ} (w : Word n) :=
  repeated w 0 2 ∧ repeated w 0 4

private def double {n : ℕ} (w : Word n) :=
  repeated w 0 3 ∧ repeated w 1 4

private theorem valid_iff {n : ℕ} (w : Word n) :
    valid w ↔ ¬ (repeated w 0 2 ∨ repeated w 0 3 ∨ repeated w 0 4 ∨
      repeated w 1 3 ∨ repeated w 1 4 ∨ repeated w 2 4) := by
  constructor
  · intro hv h
    rcases h with h | h | h | h | h | h
    · exact hv 0 2 (by decide) h
    · exact hv 0 3 (by decide) h
    · exact hv 0 4 (by decide) h
    · exact hv 1 3 (by decide) h
    · exact hv 1 4 (by decide) h
    · exact hv 2 4 (by decide) h
  · intro h i j hij hr
    fin_cases i <;> fin_cases j <;> try (norm_num [Fin.lt_def] at hij)
    all_goals try (exact h (by tauto))
    all_goals
      simp [repeated, Fin.ext_iff] at hr
      omega

private theorem overlap_control {n : ℕ} (w : Word n) :
    (repeated w 0 2 ∧ repeated w 0 4 ↔ repeated w 0 2 ∧ repeated w 2 4) ∧
    (repeated w 0 2 ∧ repeated w 0 4 ↔ repeated w 0 4 ∧ repeated w 2 4) ∧
    ¬ (repeated w 0 2 ∧ repeated w 0 3) ∧
    ¬ (repeated w 0 2 ∧ repeated w 1 3) ∧
    ¬ (repeated w 0 2 ∧ repeated w 1 4) ∧
    ¬ (repeated w 0 3 ∧ repeated w 0 4) ∧
    ¬ (repeated w 0 3 ∧ repeated w 1 3) ∧
    ¬ (repeated w 0 3 ∧ repeated w 2 4) ∧
    ¬ (repeated w 0 4 ∧ repeated w 1 3) ∧
    ¬ (repeated w 0 4 ∧ repeated w 1 4) ∧
    ¬ (repeated w 1 3 ∧ repeated w 1 4) ∧
    ¬ (repeated w 1 3 ∧ repeated w 2 4) ∧
    ¬ (repeated w 1 4 ∧ repeated w 2 4) := by
  simp [repeated, Fin.ext_iff]
  omega

private noncomputable def ind (p : Prop) : ℤ := if p then 1 else 0

set_option maxHeartbeats 3000000 in
private theorem indicators {n : ℕ} (w : Word n) :
    ind (valid w) = 1 -
      (ind (repeated w 0 2) + ind (repeated w 0 3) + ind (repeated w 0 4) +
       ind (repeated w 1 3) + ind (repeated w 1 4) + ind (repeated w 2 4)) +
      2 * ind (triple w) + ind (double w) := by
  have h := overlap_control w
  have hv := valid_iff w
  simp only [ind]
  split_ifs <;> simp_all [triple, double]

private theorem canonical_card (n : ℕ) :
    Fintype.card {w : Word n // repeated w 0 2} = n * (n+1)^2 := by
  let e : {w : Word n // repeated w 0 2} ≃ (Fin n × Fin (n+1) × Fin (n+1)) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h : (w.1 0).val + 1 = (w.1 1).val := w.2.1
      have hlt := (w.1 1).isLt
      omega⟩, w.1 4, w.1 5)
    invFun := fun t => ⟨word t.1.castSucc t.1.succ t.1.castSucc t.1.succ t.2.1 t.2.2, by
      change (t.1.castSucc).val + 1 = (t.1.succ).val ∧ _ = _ ∧ _ = _
      exact ⟨rfl, rfl, rfl⟩⟩
    left_inv := fun w => by
      have h1 : (w.1 0).val + 1 = (w.1 1).val := w.2.1
      have h2 : w.1 0 = w.1 2 := w.2.2.1
      have h3 : w.1 1 = w.1 3 := w.2.2.2
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, Fin.ext_iff] at * <;> omega
    right_inv := fun t => by
      rcases t with ⟨x,y,z⟩
      rfl }
  simpa [pow_two, mul_assoc] using Fintype.card_congr e

private theorem repeat_card (n : ℕ) (i j : Fin 5) (p : Equiv.Perm (Fin 6))
    (h0 : p 0 = i.castSucc) (h1 : p 1 = i.succ)
    (h2 : p 2 = j.castSucc) (h3 : p 3 = j.succ) :
    Fintype.card {w : Word n // repeated w i j} = n * (n+1)^2 := by
  let e : {w : Word n // repeated w i j} ≃ {w : Word n // repeated w 0 2} := {
    toFun := fun w => ⟨fun k => w.1 (p k), by
      change (w.1 (p 0)).val + 1 = (w.1 (p 1)).val ∧
        w.1 (p 0) = w.1 (p 2) ∧ w.1 (p 1) = w.1 (p 3)
      simpa only [h0, h1, h2, h3, repeated] using w.2⟩
    invFun := fun w => ⟨fun k => w.1 (p.symm k), by
      change (w.1 (p.symm i.castSucc)).val + 1 = (w.1 (p.symm i.succ)).val ∧
        w.1 (p.symm i.castSucc) = w.1 (p.symm j.castSucc) ∧
        w.1 (p.symm i.succ) = w.1 (p.symm j.succ)
      rw [← h0, ← h1, ← h2, ← h3]
      simpa [repeated] using w.2⟩
    left_inv := fun w => by
      apply Subtype.ext
      funext k
      change w.1 (p (p.symm k)) = w.1 k
      simp
    right_inv := fun w => by
      apply Subtype.ext
      funext k
      change w.1 (p.symm (p k)) = w.1 k
      simp }
  exact (Fintype.card_congr e).trans (canonical_card n)

private theorem count03 (n : ℕ) :
    Fintype.card {w : Word n // repeated w 0 3} = n * (n+1)^2 :=
  repeat_card n 0 3 ((Equiv.swap 2 3).trans (Equiv.swap 2 4)) rfl rfl rfl rfl

private theorem count04 (n : ℕ) :
    Fintype.card {w : Word n // repeated w 0 4} = n * (n+1)^2 :=
  repeat_card n 0 4 ((Equiv.swap 2 4).trans (Equiv.swap 3 5)) rfl rfl rfl rfl

private theorem count13 (n : ℕ) :
    Fintype.card {w : Word n // repeated w 1 3} = n * (n+1)^2 :=
  repeat_card n 1 3 (((Equiv.swap 0 1).trans (Equiv.swap 0 2)).trans
    ((Equiv.swap 0 3).trans (Equiv.swap 0 4))) rfl rfl rfl rfl

private theorem count14 (n : ℕ) :
    Fintype.card {w : Word n // repeated w 1 4} = n * (n+1)^2 :=
  repeat_card n 1 4 (((Equiv.swap 0 1).trans (Equiv.swap 0 2)).trans
    ((Equiv.swap 0 4).trans (Equiv.swap 3 5))) rfl rfl rfl rfl

private theorem count24 (n : ℕ) :
    Fintype.card {w : Word n // repeated w 2 4} = n * (n+1)^2 :=
  repeat_card n 2 4 (((Equiv.swap 0 2).trans (Equiv.swap 0 4)).trans
    ((Equiv.swap 1 3).trans (Equiv.swap 1 5))) rfl rfl rfl rfl

private theorem triple_card (n : ℕ) :
    Fintype.card {w : Word n // triple w} = n := by
  let e : {w : Word n // triple w} ≃ Fin n := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h : (w.1 0).val + 1 = (w.1 1).val := w.2.1.1
      have hlt := (w.1 1).isLt
      omega⟩
    invFun := fun x => ⟨word x.castSucc x.succ x.castSucc x.succ x.castSucc x.succ,
      ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩⟩
    left_inv := fun w => by
      have h1 : (w.1 0).val + 1 = (w.1 1).val := w.2.1.1
      have h2 : w.1 0 = w.1 2 := w.2.1.2.1
      have h3 : w.1 1 = w.1 3 := w.2.1.2.2
      have h4 : w.1 0 = w.1 4 := w.2.2.2.1
      have h5 : w.1 1 = w.1 5 := w.2.2.2.2
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, Fin.ext_iff] at * <;> omega
    right_inv := fun _ => rfl }
  simpa using Fintype.card_congr e

private def doubleWord {n : ℕ} (x : Fin (n - 1)) : Word n :=
  let a : Fin (n + 1) := ⟨x.val, by have h := x.isLt; omega⟩
  let b : Fin (n + 1) := ⟨x.val + 1, by have h := x.isLt; omega⟩
  let c : Fin (n + 1) := ⟨x.val + 2, by have h := x.isLt; omega⟩
  word a b c a b c

private theorem double_card (n : ℕ) :
    Fintype.card {w : Word n // double w} = n - 1 := by
  let e : {w : Word n // double w} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h1 : (w.1 0).val + 1 = (w.1 1).val := w.2.1.1
      have h2 : (w.1 1).val + 1 = (w.1 2).val := w.2.2.1
      have hlt := (w.1 2).isLt
      omega⟩
    invFun := fun x => ⟨doubleWord x, ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩⟩
    left_inv := fun w => by
      have h1 : (w.1 0).val + 1 = (w.1 1).val := w.2.1.1
      have h2 : (w.1 1).val + 1 = (w.1 2).val := w.2.2.1
      have h3 : w.1 0 = w.1 3 := w.2.1.2.1
      have h4 : w.1 1 = w.1 4 := w.2.1.2.2
      have h5 : w.1 2 = w.1 5 := w.2.2.2.2
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [doubleWord, word, Fin.ext_iff] at * <;> omega
    right_inv := fun _ => rfl }
  simpa using Fintype.card_congr e

open scoped BigOperators

private theorem sum_ind {ι : Type*} [Fintype ι] (p : ι → Prop) :
    (∑ x, ind (p x)) = (Fintype.card {x // p x} : ℤ) := by
  rw [Fintype.card_subtype]
  exact Finset.sum_boole p _

private def poly (x : ℤ) : ℤ :=
  x ^ 6 + 6 * x ^ 5 + 15 * x ^ 4 + 14 * x ^ 3 + 3 * x ^ 2 + 3 * x

private theorem a_poly (n : ℕ) : a n = poly n := by
  by_cases hn : n = 0
  · subst n
    simp [a, poly]
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Word n))) rfl
    (fun w _ => indicators w)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ind,
    canonical_card, count03, count04, count13, count14, count24, triple_card, double_card,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun,
    Fintype.card_fin] at h
  rw [a, if_neg hn]
  change (Nat.card {w : Word n // valid w} : ℤ) = poly n
  rw [Nat.card_eq_fintype_card, h]
  push_cast [Int.ofNat_sub (show 1 ≤ n by omega)]
  unfold poly
  ring

private theorem recurrence (n : ℕ) (hn : 7 ≤ n) :
    a n = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) -
      35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  simp only [a_poly, Int.natCast_sub (show 1 ≤ n by omega),
    Int.natCast_sub (show 2 ≤ n by omega), Int.natCast_sub (show 3 ≤ n by omega),
    Int.natCast_sub (show 4 ≤ n by omega), Int.natCast_sub (show 5 ≤ n by omega),
    Int.natCast_sub (show 6 ≤ n by omega), Int.natCast_sub hn, Nat.cast_ofNat]
  unfold poly
  ring

open PowerSeries

private theorem generating_function :
    (1 - X) ^ 7 * mk a = 2 * X *
      (21 + 166 * X + 158 * X ^ 2 + 17 * X ^ 4 - 2 * X ^ 5) := by
  have hd : ((1 - X) : PowerSeries ℤ) ^ 7 =
      1 - C 7 * X ^ 1 + C 21 * X ^ 2 - C 35 * X ^ 3 + C 35 * X ^ 4 -
        C 21 * X ^ 5 + C 7 * X ^ 6 - X ^ 7 := by
    norm_num
    ring
  have hq : (2 : PowerSeries ℤ) * X *
      (21 + 166 * X + 158 * X ^ 2 + 17 * X ^ 4 - 2 * X ^ 5) =
      C 42 * X ^ 1 + C 332 * X ^ 2 + C 316 * X ^ 3 + C 34 * X ^ 5 - C 4 * X ^ 6 := by
    norm_num
    ring
  rw [hd, hq]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n < 7
  · interval_cases n <;> norm_num [a_poly, poly]
  · have h1 : 1 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have h3 : 3 ≤ n := by omega
    have h4 : 4 ≤ n := by omega
    have h5 : 5 ≤ n := by omega
    have h6 : 6 ≤ n := by omega
    have h7 : 7 ≤ n := by omega
    simp only [if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6,
      if_pos h7, if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega), mul_zero, add_zero, sub_zero]
    have hr := recurrence n h7
    omega

end A269659Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a269659.main :=
  ⟨A269659Proof.generating_function, fun n hn => A269659Proof.recurrence n (by omega)⟩
