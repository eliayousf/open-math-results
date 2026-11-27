import OMAStatements.S_oeis_a084043
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Fintype.Pigeonhole

open OMA.S_oeis_a084043

namespace A084043Proof

private theorem decimal_period (n : ℕ) (hn : 0 < n) :
    ∃ k d : ℕ, 0 < d ∧ ∀ t : ℕ, 10 ^ k * 10 ^ (d * t) ≡ 10 ^ k [MOD n] := by
  let f (i : Fin (n + 1)) : Fin n := ⟨10 ^ i.val % n, Nat.mod_lt _ hn⟩
  obtain ⟨i, j, hij, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have hmod : (10 : ℕ) ^ i.val ≡ 10 ^ j.val [MOD n] := congrArg Fin.val he
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have step (k l : ℕ) (hlt : k < l) (hkl : 10 ^ l ≡ 10 ^ k [MOD n]) :
      ∃ k d : ℕ, 0 < d ∧ ∀ t : ℕ, 10 ^ k * 10 ^ (d * t) ≡ 10 ^ k [MOD n] := by
    let d := l - k
    have hd : 0 < d := by omega
    have hh : (10 : ℕ) ^ k * 10 ^ d ≡ 10 ^ k [MOD n] := by
      rw [← pow_add, show k + d = l by omega]
      exact hkl
    refine ⟨k, d, hd, fun t => ?_⟩
    induction t with
    | zero => simp [Nat.ModEq]
    | succ t ih =>
      rw [Nat.mul_succ, pow_add, ← mul_assoc]
      exact (ih.mul_right _).trans hh
  rcases lt_or_gt_of_ne hne with h | h
  · exact step _ _ h hmod.symm
  · exact step _ _ h hmod

private def copies (word : List ℕ) : ℕ → List ℕ
  | 0 => []
  | t + 1 => word ++ copies word t

private theorem copies_append (word : List ℕ) (t : ℕ) :
    copies word t ++ word = word ++ copies word t := by
  induction t with
  | zero => simp [copies]
  | succ t ih => simp only [copies, List.append_assoc, ih]

private theorem copies_palindrome {word : List ℕ} (h : word.reverse = word) (t : ℕ) :
    (copies word t).reverse = copies word t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [copies, List.reverse_append, ih, h, copies_append]

private theorem copies_digits {word : List ℕ} (h : ∀ a ∈ word, a < 10) (t : ℕ) :
    ∀ a ∈ copies word t, a < 10 := by
  induction t with
  | zero => simp [copies]
  | succ t ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h _ ha
    · exact ih _ ha

private theorem value_copies {word : List ℕ} {n : ℕ}
    (h : 10 ^ word.length * Nat.ofDigits 10 word ≡ Nat.ofDigits 10 word [MOD n]) (t : ℕ) :
    Nat.ofDigits 10 (copies word t) ≡ t * Nat.ofDigits 10 word [MOD n] := by
  induction t with
  | zero => simp [copies, Nat.ModEq]
  | succ t ih =>
    rw [copies, Nat.ofDigits_append, Nat.succ_mul]
    have hstep := (ih.mul_left (10 ^ word.length)).trans (by
      simpa only [mul_left_comm] using h.mul_left t)
    simpa [add_comm] using (Nat.ModEq.refl (Nat.ofDigits 10 word)).add hstep

private theorem last_nonzero_of_palindrome {word : List ℕ} {a : ℕ} {tail : List ℕ}
    (hpal : word.reverse = word) (hfirst : word = a :: tail) (ha : a ≠ 0) :
    ∀ h : word ≠ [], word.getLast h ≠ 0 := by
  have hlast : word = tail.reverse ++ [a] := by
    rw [← hpal, hfirst, List.reverse_cons]
  intro h
  simp [hlast, ha]

set_option maxHeartbeats 2000000 in
private theorem exists_admissible (n : ℕ) (hn : 0 < n) (h10 : ¬ 10 ∣ n) :
    ∃ m, admissible n m := by
  obtain ⟨k, d, hd, hperiod⟩ := decimal_period n hn
  let digits := Nat.digits 10 n
  have hdigits : digits ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne'
  have hdigit : n % 10 ≠ 0 := fun h => h10 (Nat.dvd_of_mod_eq_zero h)
  have hdr : digits = n % 10 :: Nat.digits 10 (n / 10) :=
    Nat.digits_eq_cons_digits_div (by decide) hn.ne'
  let left := digits ++ List.replicate k 0
  let half := left ++ digits
  let width := 2 * half.length
  let pad := d * (width + 1) - width
  let center := List.replicate pad 0
  let word := half ++ center ++ half.reverse
  have hlength : word.length = d * (width + 1) := by
    have hw : width ≤ d * (width + 1) := by
      have h := Nat.mul_le_mul_right (width + 1) (show 1 ≤ d by omega)
      omega
    have hp : width + pad = d * (width + 1) := Nat.add_sub_of_le hw
    simpa [word, center, width, two_mul, add_assoc, add_left_comm, add_comm] using hp
  have hpal : word.reverse = word := by
    simp [word, center, List.append_assoc]
  have hleft : left ≠ [] := by simp [left, hdigits]
  have hhalf : half ≠ [] := by simp [half, hleft]
  have hlow : Nat.ofDigits 10 left = n := by
    simp [left, digits, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
  let rest := digits ++ center ++ half.reverse
  have hword : word = left ++ rest := by simp [word, half, rest, List.append_assoc]
  have hval : Nat.ofDigits 10 word =
      n + 10 ^ k * (10 ^ digits.length * Nat.ofDigits 10 rest) := by
    rw [hword, Nat.ofDigits_append, hlow]
    simp only [left, List.length_append, List.length_replicate, pow_add]
    ring
  have hstable : 10 ^ word.length * Nat.ofDigits 10 word ≡ Nat.ofDigits 10 word [MOD n] := by
    rw [hlength, hval, mul_add]
    let B := (10 : ℕ) ^ (d * (width + 1))
    let C := (10 : ℕ) ^ digits.length * Nat.ofDigits 10 rest
    change B * n + B * (10 ^ k * C) ≡ n + 10 ^ k * C [MOD n]
    have hz : n ≡ 0 [MOD n] := by simp [Nat.ModEq]
    have hp : 10 ^ k * B * C ≡ 10 ^ k * C [MOD n] := (hperiod (width + 1)).mul_right C
    rw [show B * (10 ^ k * C) = 10 ^ k * B * C by ac_rfl]
    exact ((hz.mul_left B).add hp).trans ((hz.add (Nat.ModEq.refl _)).symm)
  have hvalid : ∀ a ∈ word, a < 10 := by
    intro a ha
    have hh : a ∈ digits ∨ a = 0 := by
      simp only [word, half, left, center, List.mem_append, List.mem_reverse, List.mem_replicate] at ha
      tauto
    rcases hh with hh | rfl
    · exact Nat.digits_lt_base (by decide) hh
    · decide
  let full := copies word n
  have hfull : full = word ++ copies word (n - 1) := by
    conv_lhs => unfold full; rw [show n = (n - 1) + 1 by omega]
    rfl
  have hfirst : ∃ tail, full = n % 10 :: tail := by
    rw [hfull, hword]
    simp only [left, hdr, List.cons_append]
    exact ⟨_, rfl⟩
  obtain ⟨tail, hfirst⟩ := hfirst
  have hrev : full.reverse = full := copies_palindrome hpal _
  let m := Nat.ofDigits 10 full
  have hmDigits : Nat.digits 10 m = full :=
    Nat.digits_ofDigits _ (by decide) _ (copies_digits hvalid _)
      (last_nonzero_of_palindrome hrev hfirst hdigit)
  have hmPos : 0 < m := by
    by_contra! h
    have hz : m = 0 := by omega
    rw [hz, Nat.digits_zero, hfirst] at hmDigits
    contradiction
  have hmMod : m ≡ 0 [MOD n] :=
    (value_copies hstable n).trans (by simp [Nat.ModEq])
  refine ⟨m, hmPos, Nat.dvd_of_mod_eq_zero hmMod, ?_, ?_⟩
  · rw [hmDigits, hrev]
  · refine ⟨left, center ++ half.reverse ++ copies word (n - 1), hleft, ?_, ?_⟩
    · simp [hhalf]
    · rw [hmDigits, hfull]
      simp [word, half, digits, List.append_assoc]

private theorem not_admissible_of_dvd {n m : ℕ} (h : 10 ∣ n) : ¬ admissible n m := by
  rintro ⟨hm, hnm, hpal, -⟩
  have hmd := Nat.mod_eq_zero_of_dvd (h.trans hnm)
  have hfirst : Nat.digits 10 m = 0 :: Nat.digits 10 (m / 10) := by
    rw [Nat.digits_eq_cons_digits_div (by decide) hm.ne', hmd]
  have hnonzero := Nat.getLast_digit_ne_zero 10 hm.ne'
  have hz : Nat.digits 10 m = (Nat.digits 10 (m / 10)).reverse ++ [0] := by
    conv_lhs => rw [← hpal, hfirst, List.reverse_cons]
  exact hnonzero (by simp [hz])

end A084043Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a084043.main := by
  open Classical A084043Proof in
  intro n hn
  by_cases h : 10 ∣ n
  · have hnone : ¬ ∃ m, admissible n m := fun ⟨_, hm⟩ => not_admissible_of_dvd h hm
    simp [a, h, hnone]
  · have hex := exists_admissible n hn h
    have hpos := (Nat.find_spec hex).1
    simp [a, h, hex, hpos.ne']
