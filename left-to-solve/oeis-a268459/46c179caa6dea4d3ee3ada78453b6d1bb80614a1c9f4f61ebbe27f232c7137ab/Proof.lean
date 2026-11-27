import OMAStatements.S_oeis_a268459
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace A268459Proof

open OMA.S_oeis_a268459

open scoped Classical

abbrev Word (n : ℕ) := Fin 5 → Fin (n + 1)

private def tuple {α : Type*} (a b c d e : α) (i : Fin 5) : α :=
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | _ => e

@[simp] private theorem cast0 : (0 : Fin 4).castSucc = (0 : Fin 5) := rfl
@[simp] private theorem cast1 : (1 : Fin 4).castSucc = (1 : Fin 5) := rfl
@[simp] private theorem cast2 : (2 : Fin 4).castSucc = (2 : Fin 5) := rfl
@[simp] private theorem cast3 : (3 : Fin 4).castSucc = (3 : Fin 5) := rfl
@[simp] private theorem succ0 : (0 : Fin 4).succ = (1 : Fin 5) := rfl
@[simp] private theorem succ1 : (1 : Fin 4).succ = (2 : Fin 5) := rfl
@[simp] private theorem succ2 : (2 : Fin 4).succ = (3 : Fin 5) := rfl
@[simp] private theorem succ3 : (3 : Fin 4).succ = (4 : Fin 5) := rfl


private def valid {n : ℕ} (w : Word n) :=
  ∀ i j : Fin 4, i < j → ¬ reversed w i j

private theorem valid_iff {n : ℕ} (w : Word n) :
    valid w ↔ ¬ (reversed w 0 1 ∨ reversed w 0 2 ∨ reversed w 0 3 ∨
      reversed w 1 2 ∨ reversed w 1 3 ∨ reversed w 2 3) := by
  constructor
  · intro hv h
    rcases h with h | h | h | h | h | h
    · exact hv 0 1 (by decide) h
    · exact hv 0 2 (by decide) h
    · exact hv 0 3 (by decide) h
    · exact hv 1 2 (by decide) h
    · exact hv 1 3 (by decide) h
    · exact hv 2 3 (by decide) h
  · intro h i j hij hr
    fin_cases i <;> fin_cases j <;> try (norm_num [Fin.lt_def] at hij)
    all_goals exact h (by tauto)

private theorem overlap_control {n : ℕ} (w : Word n) :
    (reversed w 0 1 ∧ reversed w 0 3 → reversed w 2 3) ∧
    (reversed w 0 1 ∧ reversed w 2 3 → reversed w 0 3) ∧
    (reversed w 0 3 ∧ reversed w 2 3 → reversed w 0 1) ∧
    ¬ (reversed w 0 1 ∧ reversed w 0 2) ∧
    ¬ (reversed w 0 1 ∧ reversed w 1 2) ∧
    ¬ (reversed w 0 1 ∧ reversed w 1 3) ∧
    ¬ (reversed w 0 2 ∧ reversed w 0 3) ∧
    ¬ (reversed w 0 2 ∧ reversed w 1 2) ∧
    ¬ (reversed w 0 2 ∧ reversed w 1 3) ∧
    ¬ (reversed w 0 2 ∧ reversed w 2 3) ∧
    ¬ (reversed w 0 3 ∧ reversed w 1 3) ∧
    ¬ (reversed w 1 2 ∧ reversed w 1 3) ∧
    ¬ (reversed w 1 2 ∧ reversed w 2 3) ∧
    ¬ (reversed w 1 3 ∧ reversed w 2 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [reversed, Fin.ext_iff] <;> omega

private noncomputable def ind (p : Prop) : ℤ := if p then 1 else 0

private theorem indicators {n : ℕ} (w : Word n) :
    ind (valid w) = 1 -
      (ind (reversed w 0 1) + ind (reversed w 0 2) + ind (reversed w 0 3) +
       ind (reversed w 1 2) + ind (reversed w 1 3) + ind (reversed w 2 3)) +
      2 * ind (reversed w 0 1 ∧ reversed w 0 3) + ind (reversed w 0 3 ∧ reversed w 1 2) := by
  rcases overlap_control w with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  simp only [ind, valid_iff]
  all_goals by_cases h01 : reversed w 0 1 <;> simp_all
  all_goals by_cases h02 : reversed w 0 2 <;> simp_all
  all_goals by_cases h03 : reversed w 0 3 <;> simp_all
  all_goals by_cases h12 : reversed w 1 2 <;> simp_all
  all_goals by_cases h13 : reversed w 1 3 <;> simp_all
  all_goals by_cases h23 : reversed w 2 3 <;> simp_all

private def translate {n width : ℕ} (x : Fin (n + 1 - width)) (offset : Fin (width + 1)) :
    Fin (n + 1) :=
  ⟨x.val + offset.val, by have hx := x.isLt; have ho := offset.isLt; omega⟩

-- The pattern 010ab uses digit offsets from a common base and independent letters a and b.
private theorem count01 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1} = n * (n + 1) ^ 2 := by
  let word := fun (x : Fin (n)) (a b : Fin (n + 1)) => tuple (translate (width := 1) x 0) (translate (width := 1) x 1) (translate (width := 1) x 0) a b
  let e : {w : Word n // reversed w 0 1} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 3, w.1 4)
    invFun := fun t => ⟨word t.1 t.2.1 t.2.2, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_prod, Nat.card_fin, pow_two, mul_assoc] using Nat.card_congr e

-- The pattern 0110a uses digit offsets from a common base and independent letters a and b.
private theorem count02 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 2} = n * (n + 1) := by
  let word := fun (x : Fin (n)) (a : Fin (n + 1)) => tuple (translate (width := 1) x 0) (translate (width := 1) x 1) (translate (width := 1) x 1) (translate (width := 1) x 0) a
  let e : {w : Word n // reversed w 0 2} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 4)
    invFun := fun t => ⟨word t.1 t.2, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- The pattern 01a10 uses digit offsets from a common base and independent letters a and b.
private theorem count03 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 3} = n * (n + 1) := by
  let word := fun (x : Fin (n)) (a : Fin (n + 1)) => tuple (translate (width := 1) x 0) (translate (width := 1) x 1) a (translate (width := 1) x 1) (translate (width := 1) x 0)
  let e : {w : Word n // reversed w 0 3} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 2)
    invFun := fun t => ⟨word t.1 t.2, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- The pattern a010b uses digit offsets from a common base and independent letters a and b.
private theorem count12 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 2} = n * (n + 1) ^ 2 := by
  let word := fun (x : Fin (n)) (a b : Fin (n + 1)) => tuple a (translate (width := 1) x 0) (translate (width := 1) x 1) (translate (width := 1) x 0) b
  let e : {w : Word n // reversed w 1 2} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0, w.1 4)
    invFun := fun t => ⟨word t.1 t.2.1 t.2.2, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_prod, Nat.card_fin, pow_two, mul_assoc] using Nat.card_congr e

-- The pattern a0110 uses digit offsets from a common base and independent letters a and b.
private theorem count13 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 3} = n * (n + 1) := by
  let word := fun (x : Fin (n)) (a : Fin (n + 1)) => tuple a (translate (width := 1) x 0) (translate (width := 1) x 1) (translate (width := 1) x 1) (translate (width := 1) x 0)
  let e : {w : Word n // reversed w 1 3} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0)
    invFun := fun t => ⟨word t.1 t.2, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_congr e

-- The pattern ab010 uses digit offsets from a common base and independent letters a and b.
private theorem count23 (n : ℕ) :
    Nat.card {w : Word n // reversed w 2 3} = n * (n + 1) ^ 2 := by
  let word := fun (x : Fin (n)) (a b : Fin (n + 1)) => tuple a b (translate (width := 1) x 0) (translate (width := 1) x 1) (translate (width := 1) x 0)
  let e : {w : Word n // reversed w 2 3} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 2).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩, w.1 0, w.1 1)
    invFun := fun t => ⟨word t.1 t.2.1 t.2.2, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_prod, Nat.card_fin, pow_two, mul_assoc] using Nat.card_congr e

-- The pattern 01010 uses digit offsets from a common base and independent letters a and b.
private theorem count0103 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 3} = n := by
  let word := fun (x : Fin (n)) => tuple (translate (width := 1) x 0) (translate (width := 1) x 1) (translate (width := 1) x 0) (translate (width := 1) x 1) (translate (width := 1) x 0)
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 3} ≃ Fin n := {
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

-- The pattern 01210 uses digit offsets from a common base and independent letters a and b.
private theorem count0312 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 3 ∧ reversed w 1 2} = n - 1 := by
  let word := fun (x : Fin (n - 1)) => tuple (translate (width := 2) x 0) (translate (width := 2) x 1) (translate (width := 2) x 2) (translate (width := 2) x 1) (translate (width := 2) x 0)
  let e : {w : Word n // reversed w 0 3 ∧ reversed w 1 2} ≃ Fin (n - 1) := {
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

open scoped BigOperators

private theorem sum_ind {ι : Type*} [Fintype ι] (p : ι → Prop) :
    (∑ x, ind (p x)) = (Nat.card {x // p x} : ℤ) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.sum_boole p _

private def poly (x : ℤ) : ℤ :=
  x ^ 5 + 5 * x ^ 4 + 7 * x ^ 3 + x ^ 2 + 2 * x

private theorem a_poly (n : ℕ) : a n = poly n := by
  by_cases hn : n = 0
  · subst n
    simp [a, poly]
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Word n))) rfl
    (fun w _ => indicators w)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ind,
    count01, count02, count03, count12, count13, count23, count0103, count0312,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun,
    Fintype.card_fin] at h
  rw [a, if_neg hn]
  change (Nat.card {w : Word n // valid w} : ℤ) = poly n
  rw [h]
  push_cast [Int.ofNat_sub (show 1 ≤ n by omega)]
  unfold poly
  ring

private theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    a n = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  simp only [a_poly, Int.natCast_sub (show 1 ≤ n by omega),
    Int.natCast_sub (show 2 ≤ n by omega), Int.natCast_sub (show 3 ≤ n by omega),
    Int.natCast_sub (show 4 ≤ n by omega), Int.natCast_sub (show 5 ≤ n by omega),
    Int.natCast_sub hn, Nat.cast_ofNat]
  unfold poly
  ring

open PowerSeries

private theorem generating_function :
    (1 - X) ^ 6 * mk a = 4 * X * (4 + 20 * X + 9 * X ^ 2 - 4 * X ^ 3 + X ^ 4) := by
  have hd : ((1 - X) : PowerSeries ℤ) ^ 6 =
      1 - C 6 * X ^ 1 + C 15 * X ^ 2 - C 20 * X ^ 3 + C 15 * X ^ 4 -
        C 6 * X ^ 5 + X ^ 6 := by
    norm_num
    ring
  have hq : (4 : PowerSeries ℤ) * X * (4 + 20 * X + 9 * X ^ 2 - 4 * X ^ 3 + X ^ 4) =
      C 16 * X ^ 1 + C 80 * X ^ 2 + C 36 * X ^ 3 - C 16 * X ^ 4 + C 4 * X ^ 5 := by
    norm_num
    ring
  rw [hd, hq]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n < 6
  · interval_cases n <;> norm_num [a_poly, poly]
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega),
      if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega), mul_zero, add_zero, sub_zero]
    have hr := recurrence n (by omega)
    omega

end A268459Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a268459.main :=
  ⟨A268459Proof.generating_function, fun n hn => A268459Proof.recurrence n (by omega)⟩
