import OMAStatements.S_oeis_a268460
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace A268460Proof

open OMA.S_oeis_a268460

open scoped Classical

abbrev Word (n : ℕ) := Fin 6 → Fin (n + 1)

private def tuple {α : Type*} (a b c d e f : α) (i : Fin 6) : α :=
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
@[simp] private theorem succ0 : (0 : Fin 5).succ = (1 : Fin 6) := rfl
@[simp] private theorem succ1 : (1 : Fin 5).succ = (2 : Fin 6) := rfl
@[simp] private theorem succ2 : (2 : Fin 5).succ = (3 : Fin 6) := rfl
@[simp] private theorem succ3 : (3 : Fin 5).succ = (4 : Fin 6) := rfl


private def valid {n : ℕ} (w : Word n) :=
  ∀ i j : Fin 5, i < j → ¬ reversed w i j

@[simp] private theorem cast4 : (4 : Fin 5).castSucc = (4 : Fin 6) := rfl
@[simp] private theorem succ4 : (4 : Fin 5).succ = (5 : Fin 6) := rfl

private theorem valid_iff {n : ℕ} (w : Word n) :
    valid w ↔ ¬ (reversed w 0 1 ∨ reversed w 0 2 ∨
      reversed w 0 3 ∨ reversed w 0 4 ∨
      reversed w 1 2 ∨ reversed w 1 3 ∨
      reversed w 1 4 ∨ reversed w 2 3 ∨
      reversed w 2 4 ∨ reversed w 3 4) := by
  constructor
  · intro hv h
    rcases h with h | h | h | h | h | h | h | h | h | h
    · exact hv 0 1 (by decide) h
    · exact hv 0 2 (by decide) h
    · exact hv 0 3 (by decide) h
    · exact hv 0 4 (by decide) h
    · exact hv 1 2 (by decide) h
    · exact hv 1 3 (by decide) h
    · exact hv 1 4 (by decide) h
    · exact hv 2 3 (by decide) h
    · exact hv 2 4 (by decide) h
    · exact hv 3 4 (by decide) h
  · intro h i j hij hr
    fin_cases i <;> fin_cases j <;> try (norm_num [Fin.lt_def] at hij)
    all_goals exact h (by tauto)

private theorem overlap_control {n : ℕ} (w : Word n) :
    (reversed w 0 1 ∧ reversed w 0 3 → reversed w 2 3) ∧
    (reversed w 0 1 ∧ reversed w 2 3 → reversed w 0 3) ∧
    (reversed w 0 1 ∧ reversed w 2 4 → reversed w 0 4) ∧
    (reversed w 0 2 ∧ reversed w 0 4 → reversed w 3 4) ∧
    (reversed w 0 2 ∧ reversed w 3 4 → reversed w 0 4) ∧
    (reversed w 0 3 ∧ reversed w 2 3 → reversed w 0 1) ∧
    (reversed w 0 4 ∧ reversed w 2 4 → reversed w 0 1) ∧
    (reversed w 1 2 ∧ reversed w 1 4 → reversed w 3 4) ∧
    (reversed w 1 2 ∧ reversed w 3 4 → reversed w 1 4) ∧
    (reversed w 1 4 ∧ reversed w 3 4 → reversed w 1 2) ∧
    ¬ (reversed w 0 1 ∧ reversed w 0 2) ∧
    ¬ (reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 2 3) ∧
    ¬ (reversed w 0 1 ∧ reversed w 1 2) ∧
    ¬ (reversed w 0 1 ∧ reversed w 1 3) ∧
    ¬ (reversed w 0 1 ∧ reversed w 1 4) ∧
    ¬ (reversed w 0 2 ∧ reversed w 0 3) ∧
    ¬ (reversed w 0 2 ∧ reversed w 1 2) ∧
    ¬ (reversed w 0 2 ∧ reversed w 1 3) ∧
    ¬ (reversed w 0 2 ∧ reversed w 1 4) ∧
    ¬ (reversed w 0 2 ∧ reversed w 2 3) ∧
    ¬ (reversed w 0 2 ∧ reversed w 2 4) ∧
    ¬ (reversed w 0 3 ∧ reversed w 0 4) ∧
    ¬ (reversed w 0 3 ∧ reversed w 1 3) ∧
    ¬ (reversed w 0 3 ∧ reversed w 1 4) ∧
    ¬ (reversed w 0 3 ∧ reversed w 2 4) ∧
    ¬ (reversed w 0 3 ∧ reversed w 3 4) ∧
    ¬ (reversed w 0 4 ∧ reversed w 1 2 ∧ reversed w 3 4) ∧
    ¬ (reversed w 0 4 ∧ reversed w 1 4) ∧
    ¬ (reversed w 1 2 ∧ reversed w 1 3) ∧
    ¬ (reversed w 1 2 ∧ reversed w 2 3) ∧
    ¬ (reversed w 1 2 ∧ reversed w 2 4) ∧
    ¬ (reversed w 1 3 ∧ reversed w 1 4) ∧
    ¬ (reversed w 1 3 ∧ reversed w 2 3) ∧
    ¬ (reversed w 1 3 ∧ reversed w 2 4) ∧
    ¬ (reversed w 1 3 ∧ reversed w 3 4) ∧
    ¬ (reversed w 1 4 ∧ reversed w 2 4) ∧
    ¬ (reversed w 2 3 ∧ reversed w 2 4) ∧
    ¬ (reversed w 2 3 ∧ reversed w 3 4) ∧
    ¬ (reversed w 2 4 ∧ reversed w 3 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [reversed, Fin.ext_iff] <;> omega

private noncomputable def ind (p : Prop) : ℤ := if p then 1 else 0

set_option maxHeartbeats 3000000 in
private theorem indicators {n : ℕ} (w : Word n) :
    ind (valid w) = 1 -
      (ind (reversed w 0 1) + ind (reversed w 0 2) +
       ind (reversed w 0 3) + ind (reversed w 0 4) +
       ind (reversed w 1 2) + ind (reversed w 1 3) +
       ind (reversed w 1 4) + ind (reversed w 2 3) +
       ind (reversed w 2 4) + ind (reversed w 3 4)) +
      ind (reversed w 0 1 ∧ reversed w 0 4) +
      ind (reversed w 0 1 ∧ reversed w 3 4) +
      ind (reversed w 0 3 ∧ reversed w 1 2) +
      ind (reversed w 0 4 ∧ reversed w 1 2) +
      ind (reversed w 0 4 ∧ reversed w 1 3) +
      ind (reversed w 0 4 ∧ reversed w 2 3) +
      ind (reversed w 0 4 ∧ reversed w 3 4) +
      ind (reversed w 1 4 ∧ reversed w 2 3) +
      2 * ind (reversed w 0 1 ∧ reversed w 0 3 ∧ reversed w 2 3) +
      ind (reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 2 4) -
      ind (reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 3 4) +
      ind (reversed w 0 2 ∧ reversed w 0 4 ∧ reversed w 3 4) +
      2 * ind (reversed w 1 2 ∧ reversed w 1 4 ∧ reversed w 3 4) := by
  rcases overlap_control w with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38⟩
  simp only [ind, valid_iff]
  all_goals by_cases h01 : reversed w 0 1 <;> simp_all
  all_goals by_cases h02 : reversed w 0 2 <;> simp_all
  all_goals by_cases h03 : reversed w 0 3 <;> simp_all
  all_goals by_cases h04 : reversed w 0 4 <;> simp_all
  all_goals by_cases h12 : reversed w 1 2 <;> simp_all
  all_goals by_cases h13 : reversed w 1 3 <;> simp_all
  all_goals by_cases h14 : reversed w 1 4 <;> simp_all
  all_goals by_cases h23 : reversed w 2 3 <;> simp_all
  all_goals by_cases h24 : reversed w 2 4 <;> simp_all
  all_goals by_cases h34 : reversed w 3 4 <;> simp_all

private def translate {n width : ℕ} (x : Fin (n + 1 - width)) (offset : Fin (width + 1)) :
    Fin (n + 1) :=
  ⟨x.val + offset.val, by have hx := x.isLt; have ho := offset.isLt; omega⟩

private theorem count01 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.1 t.2.2.1 t.2.2.2
  let e : {w : Word n // reversed w 0 1} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 3, w.1 4, w.1 5)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count02 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 2} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.1 t.2.2
  let e : {w : Word n // reversed w 0 2} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 4, w.1 5)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count03 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 3} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2.1 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2
  let e : {w : Word n // reversed w 0 3} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 2, w.1 5)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count04 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 4} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2.1 t.2.2 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 0 4} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 2, w.1 3)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count12 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 2} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2.1 t.2.2.2
  let e : {w : Word n // reversed w 1 2} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0, w.1 4, w.1 5)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count13 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 3} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2
  let e : {w : Word n // reversed w 1 3} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0, w.1 5)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count14 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 4} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2.2 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 1 4} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0, w.1 3)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count23 (n : ℕ) :
    Nat.card {w : Word n // reversed w 2 3} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 t.2.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2.2
  let e : {w : Word n // reversed w 2 3} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 2).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩, w.1 0, w.1 1, w.1 5)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count24 (n : ℕ) :
    Nat.card {w : Word n // reversed w 2 4} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 t.2.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 2 4} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 2).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩, w.1 0, w.1 1)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count34 (n : ℕ) :
    Nat.card {w : Word n // reversed w 3 4} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 t.2.2.1 t.2.2.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 3 4} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 3).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 4).isLt
      omega⟩, w.1 0, w.1 1, w.1 2)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0104 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 4} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 4} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 3)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0134 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 3 4} = n * n := by
  let word : Fin n × Fin n → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.2 0) (translate (width := 1) t.2 1) (translate (width := 1) t.2 0)
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 3 4} ≃ Fin n × Fin n := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, ⟨(w.1 3).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 4).isLt
      omega⟩)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0312 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 3 ∧ reversed w 1 2} = (n - 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) (translate (width := 2) t.1 0) t.2
  let e : {w : Word n // reversed w 0 3 ∧ reversed w 1 2} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 5)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0412 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 4 ∧ reversed w 1 2} = (n - 1) := by
  let word : Fin (n - 1) → Word n := fun t => tuple (translate (width := 2) t 0) (translate (width := 2) t 1) (translate (width := 2) t 2) (translate (width := 2) t 1) (translate (width := 2) t 1) (translate (width := 2) t 0)
  let e : {w : Word n // reversed w 0 4 ∧ reversed w 1 2} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count0413 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 4 ∧ reversed w 1 3} = (n - 1) := by
  let word : Fin (n - 1) → Word n := fun t => tuple (translate (width := 2) t 0) (translate (width := 2) t 1) (translate (width := 2) t 2) (translate (width := 2) t 2) (translate (width := 2) t 1) (translate (width := 2) t 0)
  let e : {w : Word n // reversed w 0 4 ∧ reversed w 1 3} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count0423 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 4 ∧ reversed w 2 3} = (n - 1) := by
  let word : Fin (n - 1) → Word n := fun t => tuple (translate (width := 2) t 0) (translate (width := 2) t 1) (translate (width := 2) t 1) (translate (width := 2) t 2) (translate (width := 2) t 1) (translate (width := 2) t 0)
  let e : {w : Word n // reversed w 0 4 ∧ reversed w 2 3} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count0434 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 4 ∧ reversed w 3 4} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 0 4 ∧ reversed w 3 4} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 2)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count1423 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 4 ∧ reversed w 2 3} = (n - 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) → Word n := fun t => tuple t.2 (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) (translate (width := 2) t.1 0)
  let e : {w : Word n // reversed w 1 4 ∧ reversed w 2 3} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩, w.1 0)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count010323 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 3 ∧ reversed w 2 3} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 3 ∧ reversed w 2 3} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 5)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count010424 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 2 4} = n := by
  let word : Fin n → Word n := fun t => tuple (translate (width := 1) t 0) (translate (width := 1) t 1) (translate (width := 1) t 0) (translate (width := 1) t 1) (translate (width := 1) t 1) (translate (width := 1) t 0)
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 2 4} ≃ Fin n := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count010434 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 3 4} = n := by
  let word : Fin n → Word n := fun t => tuple (translate (width := 1) t 0) (translate (width := 1) t 1) (translate (width := 1) t 0) (translate (width := 1) t 0) (translate (width := 1) t 1) (translate (width := 1) t 0)
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 3 4} ≃ Fin n := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count020434 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 2 ∧ reversed w 0 4 ∧ reversed w 3 4} = n := by
  let word : Fin n → Word n := fun t => tuple (translate (width := 1) t 0) (translate (width := 1) t 1) (translate (width := 1) t 1) (translate (width := 1) t 0) (translate (width := 1) t 1) (translate (width := 1) t 0)
  let e : {w : Word n // reversed w 0 2 ∧ reversed w 0 4 ∧ reversed w 3 4} ≃ Fin n := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count121434 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 2 ∧ reversed w 1 4 ∧ reversed w 3 4} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple t.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 1 2 ∧ reversed w 1 4 ∧ reversed w 3 4} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

open scoped BigOperators

private theorem sum_ind {ι : Type*} [Fintype ι] (p : ι → Prop) :
    (∑ x, ind (p x)) = (Nat.card {x // p x} : ℤ) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.sum_boole p _

private def poly (x : ℤ) : ℤ :=
  x ^ 6 + 6 * x ^ 5 + 11 * x ^ 4 + 2 * x ^ 3 + 6 * x - 4

private theorem a_poly (n : ℕ) (hn : 0 < n) : a n = poly n := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Word n))) rfl
    (fun w _ => indicators w)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ind,
    count01, count02, count03, count04, count12, count13, count14,
    count23, count24, count34, count0104, count0134, count0312, count0412,
    count0413, count0423, count0434, count1423, count010323, count010424, count010434,
    count020434, count121434,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun,
    Fintype.card_fin] at h
  rw [a, if_neg (show n ≠ 0 by omega)]
  change (Nat.card {w : Word n // valid w} : ℤ) = poly n
  rw [h]
  push_cast [Int.ofNat_sub (show 1 ≤ n by omega)]
  unfold poly
  ring

private theorem recurrence (n : ℕ) (hn : 7 < n) :
    a n = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) -
      35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  rw [a_poly n (by omega), a_poly (n - 1) (by omega), a_poly (n - 2) (by omega),
    a_poly (n - 3) (by omega), a_poly (n - 4) (by omega), a_poly (n - 5) (by omega),
    a_poly (n - 6) (by omega), a_poly (n - 7) (by omega)]
  simp only [Int.natCast_sub (show 1 ≤ n by omega),
    Int.natCast_sub (show 2 ≤ n by omega), Int.natCast_sub (show 3 ≤ n by omega),
    Int.natCast_sub (show 4 ≤ n by omega), Int.natCast_sub (show 5 ≤ n by omega),
    Int.natCast_sub (show 6 ≤ n by omega), Int.natCast_sub (show 7 ≤ n by omega), Nat.cast_ofNat]
  unfold poly
  ring

private theorem a_at_all (n : ℕ) : a n = if n = 0 then 0 else poly n := by
  by_cases hn : n = 0
  · simp [a, hn]
  · simpa [hn] using a_poly n (by omega)

open PowerSeries

private theorem generating_function :
    (1 - X) ^ 7 * mk a = 2 * X *
      (11 + 151 * X + 208 * X ^ 2 - 6 * X ^ 3 - 13 * X ^ 4 + 11 * X ^ 5 - 2 * X ^ 6) := by
  have hd : ((1 - X) : PowerSeries ℤ) ^ 7 =
      1 - C 7 * X ^ 1 + C 21 * X ^ 2 - C 35 * X ^ 3 + C 35 * X ^ 4 -
        C 21 * X ^ 5 + C 7 * X ^ 6 - X ^ 7 := by
    norm_num
    ring
  have hq : (2 : PowerSeries ℤ) * X *
      (11 + 151 * X + 208 * X ^ 2 - 6 * X ^ 3 - 13 * X ^ 4 + 11 * X ^ 5 - 2 * X ^ 6) =
      C 22 * X ^ 1 + C 302 * X ^ 2 + C 416 * X ^ 3 - C 12 * X ^ 4 -
        C 26 * X ^ 5 + C 22 * X ^ 6 - C 4 * X ^ 7 := by
    norm_num
    ring
  rw [hd, hq]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n < 8
  · interval_cases n <;> norm_num [a_at_all, poly]
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega), if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega), if_neg (show n ≠ 7 by omega),
      mul_zero, add_zero, sub_zero]
    have hr := recurrence n (by omega)
    omega

end A268460Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a268460.main :=
  ⟨A268460Proof.generating_function, A268460Proof.recurrence⟩
