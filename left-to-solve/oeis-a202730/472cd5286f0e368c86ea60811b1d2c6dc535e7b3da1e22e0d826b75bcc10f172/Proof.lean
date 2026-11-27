import OMAStatements.S_oeis_a202730
import Mathlib.Data.Finset.Prod
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace A202730Proof

open Finset OMA.S_oeis_a202730

private theorem mem_rows_iff (r : Row) :
    r ∈ rows ↔ isAscent [r.1,r.2.1,r.2.2] = true := by
  rcases r with ⟨x,y,z⟩
  simp only [rows, mem_insert, mem_singleton, Prod.mk.injEq, isAscent, follows,
    Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs <;> omega

private theorem cons_mem_words {r : Row} {l : List Row} {n : ℕ} :
    r :: l ∈ words (n+1) ↔ r ∈ rows ∧ l ∈ words n := by
  rw [words, mem_map]
  constructor
  · rintro ⟨⟨s,k⟩,hm,he⟩
    change s :: k = r :: l at he
    obtain ⟨rfl,rfl⟩ := List.cons.inj he
    exact mem_product.mp hm
  · intro h
    exact ⟨⟨r,l⟩, mem_product.mpr h, rfl⟩

private theorem mem_words_iff (l : List Row) (n : ℕ) :
    l ∈ words n ↔ l.length = n ∧ ∀ r ∈ l, r ∈ rows := by
  induction n generalizing l with
  | zero => cases l <;> simp [words]
  | succ n ih =>
    cases l with
    | nil =>
      simp only [words, mem_map, List.length_nil, Nat.zero_ne_add_one, false_and, iff_false]
      rintro ⟨⟨r,l⟩,_,h⟩
      cases h
    | cons r l =>
      rw [cons_mem_words, ih]
      simp only [List.length_cons, Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp]
      tauto

private theorem mem_arrays_iff (l : List Row) (n : ℕ) :
    l ∈ arrays n ↔ l.length = n ∧
      (∀ r ∈ l, isAscent [r.1,r.2.1,r.2.2] = true) ∧ condition n l = true := by
  rw [arrays, mem_filter, mem_words_iff]
  simp only [mem_rows_iff, and_assoc]

private theorem words_count (n : ℕ) : (words n).card = 5^n := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    rw [words, card_map, card_product, ih, pow_succ']
    rfl

def hasFirstOne : List Row → Bool
  | [] => false
  | r :: xs => decide (r.2.2 = 1) || (decide (r.2.2 = 0) && hasFirstOne xs)

private def zeroRows : Finset Row := {(0,0,0), (0,1,0)}
private def oneRows : Finset Row := {(0,0,1), (0,1,1)}
private def accepted (n : ℕ) : Finset (List Row) := (words n).filter (fun l => hasFirstOne l = true)

private theorem row_fields {r : Row} (h : r ∈ rows) :
    r.1 = 0 ∧ r.2.1 ≤ 1 ∧ r.2.2 ≤ 2 := by
  rcases r with ⟨x,y,z⟩
  simp only [rows, mem_insert, mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> decide

private theorem zeroRows_spec (r : Row) : r ∈ zeroRows ↔ r ∈ rows ∧ r.2.2 = 0 := by
  rcases r with ⟨x,y,z⟩
  simp only [zeroRows, rows, mem_insert, mem_singleton, Prod.mk.injEq]
  omega

private theorem oneRows_spec (r : Row) : r ∈ oneRows ↔ r ∈ rows ∧ r.2.2 = 1 := by
  rcases r with ⟨x,y,z⟩
  simp only [oneRows, rows, mem_insert, mem_singleton, Prod.mk.injEq]
  omega

private theorem filtered_prepend (F : Finset Row) (G : Finset (List Row)) (r : Row)
    (l : List Row) : r :: l ∈ (F ×ˢ G).map prepend ↔ r ∈ F ∧ l ∈ G := by
  rw [mem_map]
  constructor
  · rintro ⟨⟨s,k⟩,hm,he⟩
    change s :: k = r :: l at he
    obtain ⟨rfl,rfl⟩ := List.cons.inj he
    exact mem_product.mp hm
  · intro h
    exact ⟨⟨r,l⟩, mem_product.mpr h, rfl⟩

private theorem accepted_succ (n : ℕ) : accepted (n+1) =
    (oneRows ×ˢ words n).map prepend ∪ (zeroRows ×ˢ accepted n).map prepend := by
  ext l
  cases l with
  | nil =>
    simp only [accepted, mem_filter, hasFirstOne, Bool.false_eq_true, and_false, mem_union,
      mem_map, false_iff, not_or]
    constructor <;> rintro ⟨⟨r,l⟩,_,h⟩ <;> cases h
  | cons r l =>
    simp only [accepted, mem_filter, cons_mem_words, hasFirstOne, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, mem_union, filtered_prepend, oneRows_spec, zeroRows_spec]
    tauto

private theorem accepted_count_succ (n : ℕ) :
    (accepted (n+1)).card = 2*5^n + 2*(accepted n).card := by
  have hd : Disjoint ((oneRows ×ˢ words n).map prepend) ((zeroRows ×ˢ accepted n).map prepend) := by
    rw [Finset.disjoint_left]
    intro l h₁ h₀
    obtain ⟨⟨r,xs⟩,hx,rfl⟩ := mem_map.mp h₁
    have hpos := (oneRows_spec r).mp (mem_product.mp hx).1
    have hzero := (zeroRows_spec r).mp ((filtered_prepend _ _ r xs).mp h₀).1
    omega
  rw [accepted_succ, card_union_of_disjoint hd, card_map, card_map, card_product, card_product,
    words_count]
  rfl

private theorem accepted_closed (n : ℕ) :
    (3 : ℤ) * (accepted n).card = 2*((5 : ℤ)^n-(2 : ℤ)^n) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [accepted_count_succ]
    push_cast
    calc
      _ = 6*(5 : ℤ)^n + 2*(3*(accepted n).card : ℤ) := by ring
      _ = _ := by rw [ih, pow_succ, pow_succ]; ring

private def top : Row := (0,0,0)
private def bottom : Row := (0,1,2)

private theorem follows_of_small (l : List ℕ) (prev asc bound : ℕ) (hb : bound ≤ asc+1)
    (hsmall : ∀ v ∈ l, v ≤ bound) : follows prev asc l = true := by
  induction l generalizing prev asc with
  | nil => rfl
  | cons x xs ih =>
    have hx := hsmall x (by simp)
    simp only [follows, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, ih x (asc + if prev < x then 1 else 0) (by omega) ?_⟩
    intro y hy
    exact hsmall y (by simp [hy])

private theorem follows_terminal (l : List Row) (hr : ∀ r ∈ l, r ∈ rows) :
    follows 0 0 (l.map (fun r => r.2.2) ++ [2]) = true ↔ hasFirstOne l = true := by
  induction l with
  | nil => decide
  | cons r xs ih =>
    have hb := (row_fields (hr r (by simp))).2.2
    have htail : ∀ r ∈ xs, r ∈ rows := fun v hv => hr v (by simp [hv])
    have hz : r.2.2 = 0 ∨ r.2.2 = 1 ∨ r.2.2 = 2 := by omega
    rcases hz with h | h | h
    · simpa [hasFirstOne, List.map_cons, follows, h] using ih htail
    · have hsmall : ∀ v ∈ xs.map (fun r => r.2.2) ++ [2], v ≤ 2 := by
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · obtain ⟨r,hr₁,rfl⟩ := List.mem_map.mp hv
          exact (row_fields (htail r hr₁)).2.2
        · exact le_of_eq (List.mem_singleton.mp hv)
      have hf := follows_of_small _ 1 1 2 (by decide) hsmall
      simp [hasFirstOne, List.map_cons, follows, h, hf]
    · simp [hasFirstOne, List.map_cons, follows, h]

private def framed : List Row ↪ List Row :=
  ⟨fun l => top :: (l ++ [bottom]), by
    intro l k h
    have e := (List.cons.inj h).2
    exact List.append_cancel_right e⟩

private theorem binary_column (l : List Row) (f : Row → ℕ) (hzero : f top = 0)
    (hbound : ∀ r ∈ rows, f r ≤ 1) (hr : ∀ r ∈ l, r ∈ rows) :
    isAscent ((framed l).map f) = true := by
  have hsmall : ∀ v ∈ (l ++ [bottom]).map f, v ≤ 1 := by
    intro v hv
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hv
    rcases List.mem_append.mp hm with hm | hm
    · exact hbound r (hr r hm)
    · have he : r = bottom := List.mem_singleton.mp hm
      subst r
      exact hbound bottom (by decide)
  have hh := follows_of_small ((l ++ [bottom]).map f) 0 0 1 (by decide) hsmall
  change isAscent (f top :: (l ++ [bottom]).map f) = true
  simp only [hzero, isAscent, decide_true, Bool.true_and]
  exact hh

private theorem framed_condition (n : ℕ) (hn : 1 ≤ n) (l : List Row)
    (hr : ∀ r ∈ l, r ∈ rows) :
    condition (n+2) (framed l) = true ↔ hasFirstOne l = true := by
  have hf := binary_column l (fun r => r.1) rfl (fun r h => by rw [(row_fields h).1]; omega) hr
  have hs := binary_column l (fun r => r.2.1) rfl (fun r h => (row_fields h).2.1) hr
  have he : (framed l).getLast?.map (fun r => r.2.2) = some (min (n+2) 3 - 1) := by
    change ((top :: l) ++ [bottom]).getLast?.map (fun r => r.2.2) = _
    rw [List.getLast?_append_cons]
    simp [bottom, min_eq_right (show 3 ≤ n+2 by omega)]
  simp only [condition, hf, hs, he, decide_true, Bool.true_and, Bool.and_true]
  change isAscent (0 :: (l ++ [bottom]).map (fun r => r.2.2)) = true ↔ _
  simpa [isAscent, bottom] using follows_terminal l hr

private theorem condition_head {n : ℕ} {r : Row} {l : List Row}
    (h : condition n (r::l) = true) : r = top := by
  rcases r with ⟨x,y,z⟩
  simp only [condition, List.map_cons, isAscent, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [top, Prod.mk.injEq]
  tauto

private theorem condition_end {n : ℕ} {l : List Row}
    (h : condition n l = true) : l.getLast?.map (fun r => r.2.2) = some (min n 3 - 1) := by
  simp only [condition, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

private theorem bottom_unique {r : Row} (hr : r ∈ rows) (hz : r.2.2 = 2) : r = bottom := by
  rcases r with ⟨x,y,z⟩
  simp only [rows, mem_insert, mem_singleton, Prod.mk.injEq] at hr
  change z = 2 at hz
  simp only [bottom, Prod.mk.injEq]
  omega

private theorem array_frame (n : ℕ) (hn : 1 ≤ n) : arrays (n+2) = (accepted n).map framed := by
  ext l
  constructor
  · intro hl
    obtain ⟨hw,hc⟩ := mem_filter.mp hl
    obtain ⟨hlen,hrows⟩ := (mem_words_iff _ _).mp hw
    cases l with
    | nil => simp at hlen
    | cons r rest =>
      have htop := condition_head hc
      subst r
      have hne : rest ≠ [] := by intro h; simp [h] at hlen
      let xs := rest.dropLast
      let tail := rest.getLast hne
      have ht : xs ++ [tail] = rest := List.dropLast_append_getLast hne
      have htail : tail ∈ rows := hrows tail (by rw [← ht]; simp)
      have hend := condition_end hc
      rw [← ht] at hend
      have hz : tail.2.2 = 2 := by
        change ((top :: xs) ++ [tail]).getLast?.map (fun r => r.2.2) = _ at hend
        rw [List.getLast?_append_cons] at hend
        simpa [min_eq_right (show 3 ≤ n+2 by omega)] using hend
      have hbottom := bottom_unique htail hz
      have heq : framed xs = top :: rest := by
        change top :: (xs ++ [bottom]) = top :: rest
        rw [← hbottom, ht]
      have hlen' : xs.length = n := by
        rw [← ht] at hlen
        simp at hlen
        omega
      have hrows' : ∀ r ∈ xs, r ∈ rows := by
        intro r hr
        exact hrows r (by rw [← ht]; simp [hr])
      refine mem_map.mpr ⟨xs, ?_, heq⟩
      rw [accepted, mem_filter, mem_words_iff]
      refine ⟨⟨hlen',hrows'⟩, (framed_condition n hn xs hrows').mp ?_⟩
      simpa only [heq] using hc
  · intro hl
    obtain ⟨xs,hxs,rfl⟩ := mem_map.mp hl
    rw [accepted, mem_filter, mem_words_iff] at hxs
    obtain ⟨⟨hlen,hrows⟩,hh⟩ := hxs
    rw [arrays, mem_filter, mem_words_iff]
    refine ⟨⟨?_, ?_⟩, (framed_condition n hn xs hrows).mpr hh⟩
    · change (top :: (xs ++ [bottom])).length = n+2
      simp [hlen]
    · intro r hr
      change r ∈ top :: (xs ++ [bottom]) at hr
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | h | rfl
      · decide
      · exact hrows r h
      · decide

private theorem count_frame (n : ℕ) (hn : 1 ≤ n) : a (n+2) = (accepted n).card := by
  rw [a, array_frame n hn, card_map]

theorem closed_formula (n : ℕ) (hn : 2 < n) :
    (150 : ℤ) * a n = 4*(5 : ℤ)^n - 25*(2 : ℤ)^n := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  calc
    _ = 50 * (3 * (a (k+2) : ℤ)) := by ring
    _ = _ := by rw [count_frame k (by omega), accepted_closed]; simp only [pow_add]; ring

theorem linear_recurrence (n : ℕ) (hn : 3 ≤ n) :
    (a (n+2) : ℤ) - 7*a (n+1) + 10*a n = 0 := by
  have h : (150 : ℤ) * ((a (n+2) : ℤ) - 7*a (n+1) + 10*a n) = 0 := by
    calc
      _ = (150 : ℤ)*a (n+2) - 7*(150*a (n+1)) + 10*(150*a n) := by ring
      _ = 0 := by
        rw [closed_formula (n+2) (by omega), closed_formula (n+1) (by omega),
          closed_formula n (by omega)]
        simp only [pow_add]
        ring
  omega

private theorem a_zero : a 0 = 0 := by decide
private theorem a_one : a 1 = 1 := by decide
private theorem a_two : a 2 = 2 := by decide
private theorem a_three : a 3 = 2 := by
  have h := closed_formula 3 (by decide)
  norm_num at h
  omega
private theorem a_four : a 4 = 14 := by
  have h := closed_formula 4 (by decide)
  norm_num at h
  omega

open PowerSeries in
theorem generating_function :
    ((1 - 2*X)*(1 - 5*X) : ℤ⟦X⟧) * mk (fun n => (a n : ℤ)) =
      X * (1 - 5*X - 2*X^2 + 20*X^3) := by
  have hden : ((1-2*X)*(1-5*X) : ℤ⟦X⟧) = 1 - C 7 * X^1 + C 10 * X^2 := by
    simp only [map_ofNat]
    ring
  have hnum : (X * (1 - 5*X - 2*X^2 + 20*X^3) : ℤ⟦X⟧) =
      X^1 - C 5 * X^2 - C 2 * X^3 + C 20 * X^4 := by
    simp only [map_ofNat]
    ring
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n ≤ 4
  · interval_cases n <;> norm_num [a_zero, a_one, a_two, a_three, a_four]
  obtain ⟨k,rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  simp only [if_pos (show 1 ≤ k+2 by omega), if_pos (show 2 ≤ k+2 by omega),
    if_neg (show k+2≠1 by omega), if_neg (show k+2≠2 by omega),
    if_neg (show k+2≠3 by omega), if_neg (show k+2≠4 by omega)]
  have h := linear_recurrence k (by omega)
  exact h

open PowerSeries in
theorem main :
    (∀ n : ℕ, 2 < n → (150 : ℤ) * a n = 4*(5 : ℤ)^n - 25*(2 : ℤ)^n) ∧
    (((1 - 2*X)*(1 - 5*X) : ℤ⟦X⟧) * mk (fun n => (a n : ℤ)) =
      X * (1 - 5*X - 2*X^2 + 20*X^3)) :=
  ⟨closed_formula, generating_function⟩

end A202730Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a202730.main := A202730Proof.main
