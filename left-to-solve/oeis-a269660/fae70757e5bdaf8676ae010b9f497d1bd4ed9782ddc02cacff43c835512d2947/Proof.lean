import OMAStatements.S_oeis_a269660
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace A269660Proof

open OMA.S_oeis_a269660

open scoped Classical

abbrev Word (n : ℕ) := Fin 7 → Fin (n + 1)

private def tuple {α : Type*} (a b c d e f g : α) (i : Fin 7) : α :=
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | 5 => f
  | _ => g

@[simp] private theorem cast0 : (0 : Fin 6).castSucc = (0 : Fin 7) := rfl
@[simp] private theorem cast1 : (1 : Fin 6).castSucc = (1 : Fin 7) := rfl
@[simp] private theorem cast2 : (2 : Fin 6).castSucc = (2 : Fin 7) := rfl
@[simp] private theorem cast3 : (3 : Fin 6).castSucc = (3 : Fin 7) := rfl
@[simp] private theorem cast4 : (4 : Fin 6).castSucc = (4 : Fin 7) := rfl
@[simp] private theorem succ0 : (0 : Fin 6).succ = (1 : Fin 7) := rfl
@[simp] private theorem succ1 : (1 : Fin 6).succ = (2 : Fin 7) := rfl
@[simp] private theorem succ2 : (2 : Fin 6).succ = (3 : Fin 7) := rfl
@[simp] private theorem succ3 : (3 : Fin 6).succ = (4 : Fin 7) := rfl
@[simp] private theorem succ4 : (4 : Fin 6).succ = (5 : Fin 7) := rfl

@[simp] private theorem cast5 : (5 : Fin 6).castSucc = (5 : Fin 7) := rfl
@[simp] private theorem succ5 : (5 : Fin 6).succ = (6 : Fin 7) := rfl

private def valid {n : ℕ} (w : Word n) :=
  ∀ i j : Fin 6, i < j → ¬ repeated w i j

private theorem valid_iff {n : ℕ} (w : Word n) :
    valid w ↔ ¬ (repeated w 0 2 ∨ repeated w 0 3 ∨ repeated w 0 4 ∨ repeated w 0 5 ∨ repeated w 1 3 ∨ repeated w 1 4 ∨ repeated w 1 5 ∨ repeated w 2 4 ∨ repeated w 2 5 ∨ repeated w 3 5) := by
  constructor
  · intro hv h
    rcases h with h | h | h | h | h | h | h | h | h | h
    · exact hv 0 2 (by decide) h
    · exact hv 0 3 (by decide) h
    · exact hv 0 4 (by decide) h
    · exact hv 0 5 (by decide) h
    · exact hv 1 3 (by decide) h
    · exact hv 1 4 (by decide) h
    · exact hv 1 5 (by decide) h
    · exact hv 2 4 (by decide) h
    · exact hv 2 5 (by decide) h
    · exact hv 3 5 (by decide) h
  · intro h i j hij hr
    fin_cases i <;> fin_cases j <;> try (norm_num [Fin.lt_def] at hij)
    all_goals try (exact h (by tauto))
    all_goals
      simp [repeated, Fin.ext_iff] at hr
      omega

/- Repeated starts are compatible only in the cases counted below. -/
private theorem overlap_control {n : ℕ} (w : Word n) :
    (repeated w 0 2 ∧ repeated w 0 4 → repeated w 2 4) ∧
    (repeated w 0 2 ∧ repeated w 2 4 → repeated w 0 4) ∧
    (repeated w 0 4 ∧ repeated w 2 4 → repeated w 0 2) ∧
    (repeated w 0 2 ∧ repeated w 0 5 → repeated w 2 5) ∧
    (repeated w 0 2 ∧ repeated w 2 5 → repeated w 0 5) ∧
    (repeated w 0 5 ∧ repeated w 2 5 → repeated w 0 2) ∧
    (repeated w 0 3 ∧ repeated w 0 5 → repeated w 3 5) ∧
    (repeated w 0 3 ∧ repeated w 3 5 → repeated w 0 5) ∧
    (repeated w 0 5 ∧ repeated w 3 5 → repeated w 0 3) ∧
    (repeated w 1 3 ∧ repeated w 1 5 → repeated w 3 5) ∧
    (repeated w 1 3 ∧ repeated w 3 5 → repeated w 1 5) ∧
    (repeated w 1 5 ∧ repeated w 3 5 → repeated w 1 3) ∧
    ¬ (repeated w 0 2 ∧ repeated w 0 3) ∧
    ¬ (repeated w 0 2 ∧ repeated w 1 3) ∧
    ¬ (repeated w 0 2 ∧ repeated w 1 4) ∧
    ¬ (repeated w 0 2 ∧ repeated w 1 5) ∧
    ¬ (repeated w 0 3 ∧ repeated w 0 4) ∧
    ¬ (repeated w 0 3 ∧ repeated w 1 3) ∧
    ¬ (repeated w 0 3 ∧ repeated w 2 4) ∧
    ¬ (repeated w 0 4 ∧ repeated w 0 5) ∧
    ¬ (repeated w 0 4 ∧ repeated w 1 3) ∧
    ¬ (repeated w 0 4 ∧ repeated w 1 4) ∧
    ¬ (repeated w 0 4 ∧ repeated w 3 5) ∧
    ¬ (repeated w 0 5 ∧ repeated w 1 4) ∧
    ¬ (repeated w 0 5 ∧ repeated w 1 5) ∧
    ¬ (repeated w 1 3 ∧ repeated w 1 4) ∧
    ¬ (repeated w 1 3 ∧ repeated w 2 4) ∧
    ¬ (repeated w 1 3 ∧ repeated w 2 5) ∧
    ¬ (repeated w 1 4 ∧ repeated w 1 5) ∧
    ¬ (repeated w 1 4 ∧ repeated w 2 4) ∧
    ¬ (repeated w 1 4 ∧ repeated w 3 5) ∧
    ¬ (repeated w 1 5 ∧ repeated w 2 4) ∧
    ¬ (repeated w 1 5 ∧ repeated w 2 5) ∧
    ¬ (repeated w 2 4 ∧ repeated w 2 5) ∧
    ¬ (repeated w 2 4 ∧ repeated w 3 5) ∧
    ¬ (repeated w 2 5 ∧ repeated w 3 5) ∧
    ¬ (repeated w 0 3 ∧ repeated w 1 4 ∧ repeated w 2 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [repeated, Fin.ext_iff] <;> omega

private noncomputable def ind (p : Prop) : ℤ := if p then 1 else 0

set_option maxHeartbeats 3000000 in
private theorem indicators {n : ℕ} (w : Word n) :
    ind (valid w) = 1 - (
      ind (repeated w 0 2) + ind (repeated w 0 3) +
      ind (repeated w 0 4) + ind (repeated w 0 5) +
      ind (repeated w 1 3) + ind (repeated w 1 4) +
      ind (repeated w 1 5) + ind (repeated w 2 4) +
      ind (repeated w 2 5) + ind (repeated w 3 5)) +
      2 * ind (repeated w 0 2 ∧ repeated w 0 4) +
      2 * ind (repeated w 0 2 ∧ repeated w 0 5) +
      2 * ind (repeated w 0 3 ∧ repeated w 0 5) +
      2 * ind (repeated w 1 3 ∧ repeated w 1 5) +
      ind (repeated w 0 2 ∧ repeated w 3 5) +
      ind (repeated w 0 3 ∧ repeated w 1 4) +
      ind (repeated w 0 3 ∧ repeated w 1 5) +
      ind (repeated w 0 3 ∧ repeated w 2 5) +
      ind (repeated w 0 4 ∧ repeated w 1 5) +
      ind (repeated w 0 4 ∧ repeated w 2 5) +
      ind (repeated w 0 5 ∧ repeated w 1 3) +
      ind (repeated w 0 5 ∧ repeated w 2 4) +
      ind (repeated w 1 4 ∧ repeated w 2 5) := by
  rcases overlap_control w with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36⟩
  simp only [ind, valid_iff]
  all_goals by_cases h02 : repeated w 0 2 <;> simp_all
  all_goals by_cases h03 : repeated w 0 3 <;> simp_all
  all_goals by_cases h04 : repeated w 0 4 <;> simp_all
  all_goals by_cases h05 : repeated w 0 5 <;> simp_all
  all_goals by_cases h13 : repeated w 1 3 <;> simp_all
  all_goals by_cases h14 : repeated w 1 4 <;> simp_all
  all_goals by_cases h15 : repeated w 1 5 <;> simp_all
  all_goals by_cases h24 : repeated w 2 4 <;> simp_all
  all_goals by_cases h25 : repeated w 2 5 <;> simp_all
  all_goals by_cases h35 : repeated w 3 5 <;> simp_all

private theorem canonical_card (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 2} = n * (n+1)^3 := by
  let e : {w : Word n // repeated w 0 2} ≃ (Fin n × Fin (n+1) × Fin (n+1) × Fin (n+1)) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h : (w.1 0).val + 1 = (w.1 1).val := w.2.1
      have hlt := (w.1 1).isLt
      omega⟩, w.1 4, w.1 5, w.1 6)
    invFun := fun t => ⟨tuple t.1.castSucc t.1.succ t.1.castSucc t.1.succ t.2.1 t.2.2.1 t.2.2.2, by
      change (t.1.castSucc).val + 1 = (t.1.succ).val ∧ _ = _ ∧ _ = _
      exact ⟨rfl, rfl, rfl⟩⟩
    left_inv := fun w => by
      have h1 : (w.1 0).val + 1 = (w.1 1).val := w.2.1
      have h2 : w.1 0 = w.1 2 := w.2.2.1
      have h3 : w.1 1 = w.1 3 := w.2.2.2
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [tuple, Fin.ext_iff] at * <;> omega
    right_inv := fun t => by
      rcases t with ⟨x, y, z, t⟩
      rfl }
  simpa [Nat.card_prod, Nat.card_fin, pow_succ, mul_assoc] using Nat.card_congr e

private theorem repeat_card (n : ℕ) (i j : Fin 6) (p : Equiv.Perm (Fin 7))
    (h0 : p 0 = i.castSucc) (h1 : p 1 = i.succ)
    (h2 : p 2 = j.castSucc) (h3 : p 3 = j.succ) :
    Nat.card {w : Word n // repeated w i j} = n * (n+1)^3 := by
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
  exact (Nat.card_congr e).trans (canonical_card n)

private theorem count03 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 3} = n * (n+1)^3 :=
  repeat_card n 0 3 ((Equiv.swap 2 3).trans (Equiv.swap 2 4)) rfl rfl rfl rfl

private theorem count04 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 4} = n * (n+1)^3 :=
  repeat_card n 0 4 ((Equiv.swap 2 4).trans (Equiv.swap 3 5)) rfl rfl rfl rfl

private theorem count05 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 5} = n * (n+1)^3 :=
  repeat_card n 0 5 ((Equiv.swap 2 5).trans (Equiv.swap 3 6)) rfl rfl rfl rfl

private theorem count13 (n : ℕ) :
    Nat.card {w : Word n // repeated w 1 3} = n * (n+1)^3 :=
  repeat_card n 1 3 ((((Equiv.swap 0 1).trans (Equiv.swap 0 2)).trans (Equiv.swap 0 3)).trans (Equiv.swap 0 4)) rfl rfl rfl rfl

private theorem count14 (n : ℕ) :
    Nat.card {w : Word n // repeated w 1 4} = n * (n+1)^3 :=
  repeat_card n 1 4 ((((Equiv.swap 0 1).trans (Equiv.swap 0 2)).trans (Equiv.swap 0 4)).trans (Equiv.swap 3 5)) rfl rfl rfl rfl

private theorem count15 (n : ℕ) :
    Nat.card {w : Word n // repeated w 1 5} = n * (n+1)^3 :=
  repeat_card n 1 5 ((((Equiv.swap 0 1).trans (Equiv.swap 0 2)).trans (Equiv.swap 0 5)).trans (Equiv.swap 3 6)) rfl rfl rfl rfl

private theorem count24 (n : ℕ) :
    Nat.card {w : Word n // repeated w 2 4} = n * (n+1)^3 :=
  repeat_card n 2 4 ((((Equiv.swap 0 2).trans (Equiv.swap 1 3)).trans (Equiv.swap 0 4)).trans (Equiv.swap 1 5)) rfl rfl rfl rfl

private theorem count25 (n : ℕ) :
    Nat.card {w : Word n // repeated w 2 5} = n * (n+1)^3 :=
  repeat_card n 2 5 ((((Equiv.swap 0 2).trans (Equiv.swap 1 3)).trans (Equiv.swap 0 5)).trans (Equiv.swap 1 6)) rfl rfl rfl rfl

private theorem count35 (n : ℕ) :
    Nat.card {w : Word n // repeated w 3 5} = n * (n+1)^3 :=
  repeat_card n 3 5 ((((Equiv.swap 0 3).trans (Equiv.swap 1 4)).trans (Equiv.swap 2 5)).trans (Equiv.swap 0 6)) rfl rfl rfl rfl

private def shape {n width : ℕ} (layout : Fin 7 → Option (Fin (width + 1)))
    (x : Fin (n + 1 - width)) (y : Fin (n + 1)) : Word n :=
  fun i => match layout i with
    | none => y
    | some offset => ⟨x.val + offset.val, by
        have hx := x.isLt
        have ho := offset.isLt
        omega⟩

-- Pattern 010101*, with each digit an offset from the first free parameter.
private theorem count0204 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 2 ∧ repeated w 0 4} = (n) * (n + 1) := by
  let word := shape (n := n) (width := 1) (tuple (some 0) (some 1) (some 0) (some 1) (some 0) (some 1) none)
  let e : {w : Word n // repeated w 0 2 ∧ repeated w 0 4} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 6)
    invFun := fun t => ⟨word t.1 t.2, by simp [word, shape, tuple, repeated]⟩
    left_inv := fun w => by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, shape, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- Pattern 0101*01, with each digit an offset from the first free parameter.
private theorem count0205 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 2 ∧ repeated w 0 5} = (n) * (n + 1) := by
  let word := shape (n := n) (width := 1) (tuple (some 0) (some 1) (some 0) (some 1) none (some 0) (some 1))
  let e : {w : Word n // repeated w 0 2 ∧ repeated w 0 5} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 4)
    invFun := fun t => ⟨word t.1 t.2, by simp [word, shape, tuple, repeated]⟩
    left_inv := fun w => by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, shape, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- Pattern 01*0101, with each digit an offset from the first free parameter.
private theorem count0305 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 3 ∧ repeated w 0 5} = (n) * (n + 1) := by
  let word := shape (n := n) (width := 1) (tuple (some 0) (some 1) none (some 0) (some 1) (some 0) (some 1))
  let e : {w : Word n // repeated w 0 3 ∧ repeated w 0 5} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 2)
    invFun := fun t => ⟨word t.1 t.2, by simp [word, shape, tuple, repeated]⟩
    left_inv := fun w => by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, shape, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- Pattern *010101, with each digit an offset from the first free parameter.
private theorem count1315 (n : ℕ) :
    Nat.card {w : Word n // repeated w 1 3 ∧ repeated w 1 5} = (n) * (n + 1) := by
  let word := shape (n := n) (width := 1) (tuple none (some 0) (some 1) (some 0) (some 1) (some 0) (some 1))
  let e : {w : Word n // repeated w 1 3 ∧ repeated w 1 5} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0)
    invFun := fun t => ⟨word t.1 t.2, by simp [word, shape, tuple, repeated]⟩
    left_inv := fun w => by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, shape, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- Pattern 0101212, with each digit an offset from the first free parameter.
private theorem count0235 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 2 ∧ repeated w 3 5} = n - 1 := by
  let word := shape (n := n) (width := 2) (tuple (some 0) (some 1) (some 0) (some 1) (some 2) (some 1) (some 2))
  let e : {w : Word n // repeated w 0 2 ∧ repeated w 3 5} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      have hb := (w.1 4).isLt
      omega⟩
    invFun := fun x => ⟨word x 0, by simp [word, shape, tuple, repeated]⟩
    left_inv := fun w => by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, shape, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- Pattern 012012*, with each digit an offset from the first free parameter.
private theorem count0314 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 3 ∧ repeated w 1 4} = (n - 1) * (n + 1) := by
  let word := shape (n := n) (width := 2) (tuple (some 0) (some 1) (some 2) (some 0) (some 1) (some 2) none)
  let e : {w : Word n // repeated w 0 3 ∧ repeated w 1 4} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 6)
    invFun := fun t => ⟨word t.1 t.2, by simp [word, shape, tuple, repeated]⟩
    left_inv := fun w => by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, shape, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- Pattern 0120112, with each digit an offset from the first free parameter.
private theorem count0315 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 3 ∧ repeated w 1 5} = n - 1 := by
  let word := shape (n := n) (width := 2) (tuple (some 0) (some 1) (some 2) (some 0) (some 1) (some 1) (some 2))
  let e : {w : Word n // repeated w 0 3 ∧ repeated w 1 5} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩
    invFun := fun x => ⟨word x 0, by simp [word, shape, tuple, repeated]⟩
    left_inv := fun w => by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, shape, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- Pattern 1201201, with each digit an offset from the first free parameter.
private theorem count0325 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 3 ∧ repeated w 2 5} = n - 1 := by
  let word := shape (n := n) (width := 2) (tuple (some 1) (some 2) (some 0) (some 1) (some 2) (some 0) (some 1))
  let e : {w : Word n // repeated w 0 3 ∧ repeated w 2 5} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 2).val, by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩
    invFun := fun x => ⟨word x 0, by simp [word, shape, tuple, repeated]⟩
    left_inv := fun w => by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, shape, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- Pattern 012*012, with each digit an offset from the first free parameter.
private theorem count0415 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 4 ∧ repeated w 1 5} = (n - 1) * (n + 1) := by
  let word := shape (n := n) (width := 2) (tuple (some 0) (some 1) (some 2) none (some 0) (some 1) (some 2))
  let e : {w : Word n // repeated w 0 4 ∧ repeated w 1 5} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 3)
    invFun := fun t => ⟨word t.1 t.2, by simp [word, shape, tuple, repeated]⟩
    left_inv := fun w => by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, shape, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- Pattern 0112012, with each digit an offset from the first free parameter.
private theorem count0425 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 4 ∧ repeated w 2 5} = n - 1 := by
  let word := shape (n := n) (width := 2) (tuple (some 0) (some 1) (some 1) (some 2) (some 0) (some 1) (some 2))
  let e : {w : Word n // repeated w 0 4 ∧ repeated w 2 5} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩
    invFun := fun x => ⟨word x 0, by simp [word, shape, tuple, repeated]⟩
    left_inv := fun w => by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, shape, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- Pattern 0121201, with each digit an offset from the first free parameter.
private theorem count0513 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 5 ∧ repeated w 1 3} = n - 1 := by
  let word := shape (n := n) (width := 2) (tuple (some 0) (some 1) (some 2) (some 1) (some 2) (some 0) (some 1))
  let e : {w : Word n // repeated w 0 5 ∧ repeated w 1 3} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩
    invFun := fun x => ⟨word x 0, by simp [word, shape, tuple, repeated]⟩
    left_inv := fun w => by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, shape, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- Pattern 1201012, with each digit an offset from the first free parameter.
private theorem count0524 (n : ℕ) :
    Nat.card {w : Word n // repeated w 0 5 ∧ repeated w 2 4} = n - 1 := by
  let word := shape (n := n) (width := 2) (tuple (some 1) (some 2) (some 0) (some 1) (some 0) (some 1) (some 2))
  let e : {w : Word n // repeated w 0 5 ∧ repeated w 2 4} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 2).val, by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩
    invFun := fun x => ⟨word x 0, by simp [word, shape, tuple, repeated]⟩
    left_inv := fun w => by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, shape, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- Pattern *012012, with each digit an offset from the first free parameter.
private theorem count1425 (n : ℕ) :
    Nat.card {w : Word n // repeated w 1 4 ∧ repeated w 2 5} = (n - 1) * (n + 1) := by
  let word := shape (n := n) (width := 2) (tuple none (some 0) (some 1) (some 2) (some 0) (some 1) (some 2))
  let e : {w : Word n // repeated w 1 4 ∧ repeated w 2 5} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩, w.1 0)
    invFun := fun t => ⟨word t.1 t.2, by simp [word, shape, tuple, repeated]⟩
    left_inv := fun w => by
      have h := w.2
      simp [repeated, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, shape, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

open scoped BigOperators

private theorem sum_ind {ι : Type*} [Fintype ι] (p : ι → Prop) :
    (∑ x, ind (p x)) = (Nat.card {x // p x} : ℤ) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.sum_boole p _

private def poly (x : ℤ) : ℤ :=
  x ^ 7 + 7 * x ^ 6 + 21 * x ^ 5 + 25 * x ^ 4 + 5 * x ^ 3 + 2 * x ^ 2 + 11 * x - 8

private theorem a_poly (n : ℕ) (hn : 0 < n) : a n = poly n := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Word n))) rfl
    (fun w _ => indicators w)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ind,
    canonical_card, count03, count04, count05, count13, count14, count15, count24, count25,
    count35, count0204, count0205, count0305, count1315, count0235, count0314, count0315,
    count0325, count0415, count0425, count0513, count0524, count1425,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun,
    Fintype.card_fin] at h
  rw [a, if_neg (show n ≠ 0 by omega)]
  change (Nat.card {w : Word n // valid w} : ℤ) = poly n
  rw [h]
  push_cast [Int.ofNat_sub (show 1 ≤ n by omega)]
  unfold poly
  ring

private theorem recurrence (n : ℕ) (hn : 8 < n) :
    a n = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) -
      70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  rw [a_poly n (by omega), a_poly (n - 1) (by omega), a_poly (n - 2) (by omega),
    a_poly (n - 3) (by omega), a_poly (n - 4) (by omega), a_poly (n - 5) (by omega),
    a_poly (n - 6) (by omega), a_poly (n - 7) (by omega), a_poly (n - 8) (by omega)]
  simp only [Int.natCast_sub (show 1 ≤ n by omega),
    Int.natCast_sub (show 2 ≤ n by omega), Int.natCast_sub (show 3 ≤ n by omega),
    Int.natCast_sub (show 4 ≤ n by omega), Int.natCast_sub (show 5 ≤ n by omega),
    Int.natCast_sub (show 6 ≤ n by omega), Int.natCast_sub (show 7 ≤ n by omega),
    Int.natCast_sub (show 8 ≤ n by omega), Nat.cast_ofNat]
  unfold poly
  ring

private theorem a_at_all (n : ℕ) : a n = if n = 0 then 0 else poly n := by
  by_cases hn : n = 0
  · simp [a, hn]
  · simpa [hn] using a_poly n (by omega)

open PowerSeries

private theorem generating_function :
    (1 - X) ^ 8 * mk a = 2 * X *
      (32 + 599 * X + 1354 * X ^ 2 + 438 * X ^ 3 + 48 * X ^ 4 + 71 * X ^ 5 -
        26 * X ^ 6 + 4 * X ^ 7) := by
  have hd : ((1 - X) : PowerSeries ℤ) ^ 8 =
      1 - C 8 * X ^ 1 + C 28 * X ^ 2 - C 56 * X ^ 3 + C 70 * X ^ 4 -
        C 56 * X ^ 5 + C 28 * X ^ 6 - C 8 * X ^ 7 + X ^ 8 := by
    norm_num
    ring
  have hq : (2 : PowerSeries ℤ) * X *
      (32 + 599 * X + 1354 * X ^ 2 + 438 * X ^ 3 + 48 * X ^ 4 + 71 * X ^ 5 -
        26 * X ^ 6 + 4 * X ^ 7) =
      C 64 * X ^ 1 + C 1198 * X ^ 2 + C 2708 * X ^ 3 + C 876 * X ^ 4 +
        C 96 * X ^ 5 + C 142 * X ^ 6 - C 52 * X ^ 7 + C 8 * X ^ 8 := by
    norm_num
    ring
  rw [hd, hq]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n < 9
  · interval_cases n <;> norm_num [a_at_all, poly]
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega), if_pos (show 8 ≤ n by omega),
      if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega), if_neg (show n ≠ 8 by omega),
      mul_zero, add_zero, sub_zero]
    have hr := recurrence n (by omega)
    omega

end A269660Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a269660.main :=
  ⟨A269660Proof.generating_function, A269660Proof.recurrence⟩
