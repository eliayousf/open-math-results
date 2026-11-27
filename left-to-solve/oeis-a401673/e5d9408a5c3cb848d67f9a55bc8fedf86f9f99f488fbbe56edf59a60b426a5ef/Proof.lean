import OMAStatements.S_oeis_a401673
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace OpenMath.A401673

open OMA.S_oeis_a401673

private def evenRow {n j : ℕ} (hj : j < n) : Fin (2 * n) := ⟨2 * j, by omega⟩
private def oddRow {n j : ℕ} (hj : j < n) : Fin (2 * n) := ⟨2 * j + 1, by omega⟩

/-- Without horizontal pieces, matching partners stay in successive pairs of rows. -/
theorem partners_share_row_pair {n : ℕ} (mate : Cell n → Cell n)
    (hinv : Function.Involutive mate)
    (hstep : ∀ v, Nat.dist (mate v).1.val v.1.val = 1)
    (j : ℕ) (hj : j < n) :
    (∀ c, (mate (evenRow hj, c)).1 = oddRow hj) ∧
    (∀ c, (mate (oddRow hj, c)).1 = evenRow hj) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have forward (c : Fin (2 * n)) : (mate (evenRow hj,c)).1 = oddRow hj := by
      apply Fin.ext
      have hs := hstep (evenRow hj,c)
      unfold Nat.dist at hs
      change ((mate (evenRow hj,c)).1.val - 2*j) +
        (2*j - (mate (evenRow hj,c)).1.val) = 1 at hs
      change (mate (evenRow hj,c)).1.val = 2*j+1
      by_contra hbad
      have hjpos : 0 < j := by omega
      have hp : j - 1 < n := by omega
      have he : (mate (evenRow hj,c)).1 = oddRow hp := by
        apply Fin.ext
        change (mate (evenRow hj,c)).1.val = 2 * (j - 1) + 1
        omega
      have hb := (ih (j - 1) (by omega) hp).2 (mate (evenRow hj,c)).2
      have hv : mate (evenRow hj, c) = (oddRow hp,(mate (evenRow hj,c)).2) :=
        Prod.ext he rfl
      rw [← hv, hinv] at hb
      have hv' : 2 * j = 2 * (j - 1) :=
        congrArg Fin.val hb
      omega
    refine ⟨forward, ?_⟩
    let f (c : Fin (2 * n)) := (mate (evenRow hj,c)).2
    have hf : Function.Injective f := by
      intro a b hab
      have hab' : mate (evenRow hj,a) = mate (evenRow hj,b) :=
        Prod.ext ((forward a).trans (forward b).symm) hab
      exact congrArg Prod.snd (hinv.injective hab')
    have hsurj := Finite.injective_iff_surjective.mp hf
    intro c
    obtain ⟨b,hb⟩ := hsurj c
    have hmatch : mate (evenRow hj,b) = (oddRow hj,c) := Prod.ext (forward b) hb
    have hinv' := hinv (evenRow hj,b)
    rw [hmatch] at hinv'
    exact congrArg Prod.fst hinv'


/-- A permutation of an even-length interval that moves every point by one. -/
theorem adjacent_permutation {n : ℕ} (f : Fin (2 * n) → Fin (2 * n))
    (hinj : Function.Injective f) (hstep : ∀ v, Nat.dist (f v).val v.val = 1)
    (j : ℕ) (hj : j < n) :
    f (evenRow hj) = oddRow hj ∧ f (oddRow hj) = evenRow hj := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have heven : f (evenRow hj) = oddRow hj := by
      apply Fin.ext
      have hs := hstep (evenRow hj)
      unfold Nat.dist at hs
      change ((f (evenRow hj)).val - 2*j) + (2*j - (f (evenRow hj)).val) = 1 at hs
      change (f (evenRow hj)).val = 2*j+1
      by_contra hbad
      have hp : j - 1 < n := by omega
      have hh : f (evenRow hj) = oddRow hp := by
        apply Fin.ext
        change (f (evenRow hj)).val = 2 * (j - 1) + 1
        omega
      have hr := hinj (hh.trans (ih (j - 1) (by omega) hp).1.symm)
      have hvals : 2 * j = 2 * (j - 1) := congrArg Fin.val hr
      omega
    refine ⟨heven, ?_⟩
    obtain ⟨v,hv⟩ := Finite.injective_iff_surjective.mp hinj (evenRow hj)
    have hs := hstep v
    rw [hv] at hs
    unfold Nat.dist at hs
    change (2*j - v.val) + (v.val - 2*j) = 1 at hs
    have hpre : v = oddRow hj := by
      apply Fin.ext
      change v.val = 2*j+1
      by_contra hbad
      have hp : j - 1 < n := by omega
      have hh : v = oddRow hp := by
        apply Fin.ext
        change v.val = 2 * (j - 1) + 1
        omega
      rw [hh, (ih (j - 1) (by omega) hp).2] at hv
      have hvals : 2 * (j - 1) = 2 * j := congrArg Fin.val hv
      omega
    simpa only [hpre] using hv

private def flip {n : ℕ} (c : Fin (2 * n)) : Fin (2 * n) :=
  ⟨if c.val % 2 = 0 then c.val + 1 else c.val - 1, by
    split <;> have := c.isLt <;> omega⟩

private theorem flip_even {n j : ℕ} (hj : j < n) : flip (evenRow hj) = oddRow hj := by
  apply Fin.ext
  change (if (2*j) % 2 = 0 then 2*j+1 else 2*j-1) = 2*j+1
  simp

private theorem flip_odd {n j : ℕ} (hj : j < n) : flip (oddRow hj) = evenRow hj := by
  apply Fin.ext
  change (if (2*j+1) % 2 = 0 then 2*j+2 else 2*j+1-1) = 2*j
  rw [if_neg (by omega)]
  omega

private theorem pair_coordinate {n : ℕ} (u : Fin (2*n)) :
    ∃ j : ℕ, ∃ hj : j < n, u = evenRow hj ∨ u = oddRow hj := by
  have h := u.isLt
  refine ⟨u.val / 2, by omega, ?_⟩
  by_cases he : u.val % 2 = 0
  · left
    apply Fin.ext
    change u.val = 2 * (u.val / 2)
    omega
  · right
    apply Fin.ext
    change u.val = 2 * (u.val / 2) + 1
    omega

private theorem flip_involutive {n : ℕ} : Function.Involutive (flip (n := n)) := by
  intro u
  obtain ⟨j,hj, hu | hu⟩ := pair_coordinate u
  · rw [hu, flip_even, flip_odd]
  · rw [hu, flip_odd, flip_even]

private theorem flip_step {n : ℕ} (u : Fin (2*n)) : Nat.dist (flip u).val u.val = 1 := by
  obtain ⟨j,hj, hu | hu⟩ := pair_coordinate u
  · rw [hu, flip_even]
    change Nat.dist (2*j+1) (2*j) = 1
    unfold Nat.dist
    omega
  · rw [hu, flip_odd]
    change Nat.dist (2*j) (2*j+1) = 1
    unfold Nat.dist
    omega

private def canonical (n : ℕ) : AllDiagonal n :=
  ⟨fun u => (flip u.1, flip u.2), ⟨fun u => Prod.ext
    (flip_involutive u.1) (flip_involutive u.2),
    fun u => ⟨flip_step u.1, flip_step u.2⟩⟩⟩

private theorem fixed_row {n : ℕ} (mate : AllDiagonal n) (r s : Fin (2*n))
    (hr : ∀ c, (mate.val (r,c)).1 = s) (c : Fin (2*n)) :
    (mate.val (r,c)).2 = flip c := by
  let f (v : Fin (2*n)) := (mate.val (r,v)).2
  have hi : Function.Injective f := by
    intro x y hxy
    have hv : mate.val (r,x) = mate.val (r,y) := Prod.ext ((hr x).trans (hr y).symm) hxy
    exact congrArg Prod.snd (mate.property.1.injective hv)
  have ht (u : Fin (2*n)) : Nat.dist (f u).val u.val = 1 :=
    (mate.property.2 (r,u)).2
  obtain ⟨j,hj,hc | hc⟩ := pair_coordinate c
  · rw [hc, flip_even]
    exact (adjacent_permutation f hi ht j hj).1
  · rw [hc, flip_odd]
    exact (adjacent_permutation f hi ht j hj).2

private theorem eq_canonical {n : ℕ} (mate : AllDiagonal n) : mate = canonical n := by
  apply Subtype.ext
  funext u
  obtain ⟨r,c⟩ := u
  obtain ⟨j,hj,hr | hr⟩ := pair_coordinate r
  · subst r
    let h := (partners_share_row_pair mate.val mate.property.1
      (fun v => (mate.property.2 v).1) j hj).1
    exact Prod.ext ((h c).trans (flip_even hj).symm) (fixed_row mate _ _ h c)
  · subst r
    let h := (partners_share_row_pair mate.val mate.property.1
      (fun v => (mate.property.2 v).1) j hj).2
    exact Prod.ext ((h c).trans (flip_odd hj).symm) (fixed_row mate _ _ h c)

/-- The square with even sides has exactly one tiling using diagonals only. -/
theorem pure_count (n : ℕ) : Nonempty (Unique (AllDiagonal n)) :=
  ⟨⟨⟨canonical n⟩, eq_canonical⟩⟩

theorem diagonalCount_one (n : ℕ) : diagonalCount n = 1 := by
  have hu : Unique (AllDiagonal n) := (pure_count n).some
  exact @Fintype.card_unique (AllDiagonal n) hu (Fintype.ofFinite _)

/-- Any permutation of a line with displacement at most one consists only of
fixed points and neighboring transpositions. -/
theorem near_permutation_involutive {w : ℕ} (f : Fin w → Fin w)
    (hinj : Function.Injective f) (hstep : ∀ v, Nat.dist (f v).val v.val ≤ 1) :
    Function.Involutive f := by
  have main (k : ℕ) (hk : k < w) : f (f ⟨k,hk⟩) = ⟨k,hk⟩ := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      let v : Fin w := ⟨k,hk⟩
      change f (f v) = v
      rcases lt_trichotomy (f v).val k with hlt | heq | hgt
      · have hh : f (f (f v)) = f v := ih (f v).val hlt (f v).isLt
        exact hinj hh
      · have hv : f v = v := Fin.ext heq
        simp only [hv]
      · obtain ⟨t,ht⟩ := Finite.injective_iff_surjective.mp hinj v
        have hlo : k < t.val := by
          by_contra! hbad
          rcases lt_or_eq_of_le hbad with h | h
          · have hpair : f (f t) = t := ih t.val h t.isLt
            rw [ht] at hpair
            have hv := congrArg Fin.val hpair
            omega
          · have htv : t = v := Fin.ext h
            rw [htv] at ht
            have hvals : (f v).val = k := congrArg Fin.val ht
            omega
        have hs := hstep v
        have hts := hstep t
        rw [ht] at hts
        unfold Nat.dist at hs hts
        change ((f v).val - k) + (k - (f v).val) ≤ 1 at hs
        change (k - t.val) + (t.val - k) ≤ 1 at hts
        have htv : f v = t := Fin.ext (by omega)
        rwa [htv]
  intro v
  exact main v.val v.isLt

open Finset

private def rowColour (n i : ℕ) : Finset (Cell n) :=
  univ.filter fun v => v.1.val % 2 = i

private theorem flip_parity {a b : ℕ} (h : Nat.dist a b = 1) :
    b % 2 = 0 ↔ a % 2 = 1 := by
  unfold Nat.dist at h
  omega

private theorem equal_row_colour (n : ℕ) : (rowColour n 0).card = (rowColour n 1).card := by
  let f (u : Cell n) : Cell n := (flip u.1,u.2)
  have hi : Function.Involutive f := fun u => Prod.ext (flip_involutive u.1) rfl
  let e : Cell n ≃ Cell n := ⟨f,f,hi,hi⟩
  apply Finset.card_equiv e
  intro u
  simp only [rowColour, mem_filter, mem_univ, true_and]
  change u.1.val % 2 = 0 ↔ (flip u.1).val % 2 = 1
  exact flip_parity (flip_step u.1)

private theorem isHorizontal_mate {n : ℕ} {mate : Cell n → Cell n}
    (hinv : Function.Involutive mate) (u : Cell n) :
    isHorizontal mate (mate u) ↔ isHorizontal mate u := by
  unfold isHorizontal
  rw [hinv]
  exact eq_comm

private theorem balance_horizontal {n : ℕ} (mate : Cell n → Cell n)
    (hinv : Function.Involutive mate) (hrow : ∀ u, Nat.dist (mate u).1.val u.1.val ≤ 1) :
    ((rowColour n 0).filter (isHorizontal mate)).card =
      ((rowColour n 1).filter (isHorizontal mate)).card := by
  have hc :
      ((rowColour n 0).filter fun u => ¬ isHorizontal mate u).card =
        ((rowColour n 1).filter fun u => ¬ isHorizontal mate u).card := by
    let e : Cell n ≃ Cell n := ⟨mate,mate,hinv,hinv⟩
    apply Finset.card_equiv e
    intro u
    simp only [rowColour, mem_filter, mem_univ, true_and]
    change u.1.val % 2 = 0 ∧ ¬ isHorizontal mate u ↔
      (mate u).1.val % 2 = 1 ∧ ¬ isHorizontal mate (mate u)
    rw [isHorizontal_mate hinv]
    apply and_congr_left
    intro hx
    have hne : (mate u).1.val ≠ u.1.val := fun h => hx (Fin.ext h)
    have hd := hrow u
    have hs : Nat.dist (mate u).1.val u.1.val = 1 := by
      unfold Nat.dist at *
      omega
    exact flip_parity hs
  have h0 := Finset.card_filter_add_card_filter_not (s := rowColour n 0) (isHorizontal mate)
  have h1 := Finset.card_filter_add_card_filter_not (s := rowColour n 1) (isHorizontal mate)
  have hn := equal_row_colour n
  omega

private theorem horizontal_not_singleton {n i : ℕ} (mate : Cell n → Cell n)
    (hinv : Function.Involutive mate) (hfix : ∀ u, mate u ≠ u) :
    ((rowColour n i).filter (isHorizontal mate)).card ≠ 1 := by
  intro h
  obtain ⟨u,hu⟩ := Finset.card_eq_one.mp h
  have hmem : u ∈ (rowColour n i).filter (isHorizontal mate) := by rw [hu]; simp only [mem_singleton]
  have hdata := Finset.mem_filter.mp hmem
  have hm : mate u ∈ (rowColour n i).filter (isHorizontal mate) := by
    refine Finset.mem_filter.mpr ⟨?_, (isHorizontal_mate hinv u).2 hdata.2⟩
    simp only [rowColour, mem_filter, mem_univ, true_and] at *
    rw [show (mate u).1 = u.1 from hdata.2]
    exact hdata.1
  rw [hu, Finset.mem_singleton] at hm
  exact hfix u hm

/-- With two ordinary pieces, every ordinary piece has the same orientation. -/
theorem two_ordinary_uniform {n : ℕ} (mate : Cell n → Cell n)
    (hinv : Function.Involutive mate) (hfix : ∀ u, mate u ≠ u)
    (hrow : ∀ u, Nat.dist (mate u).1.val u.1.val ≤ 1)
    (hcol : ∀ u, Nat.dist (mate u).2.val u.2.val ≤ 1)
    (hcount : (ordinaryCells mate).card = 4) :
    (∀ u, Nat.dist (mate u).1.val u.1.val = 1) ∨
      (∀ u, Nat.dist (mate u).2.val u.2.val = 1) := by
  let allH : Finset (Cell n) := univ.filter (isHorizontal mate)
  have hsubset : allH ⊆ ordinaryCells mate := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp hu).2⟩
  have hbound := Finset.card_le_card hsubset
  have heq := balance_horizontal mate hinv hrow
  have hone := horizontal_not_singleton (i := 0) mate hinv hfix
  have hh0 : allH.filter (fun u => u.1.val % 2 = 0) =
      (rowColour n 0).filter (isHorizontal mate) := by
    ext u
    simp only [allH, rowColour, mem_filter, mem_univ, true_and, and_comm]
  have hh1 : allH.filter (fun u => ¬ u.1.val % 2 = 0) =
      (rowColour n 1).filter (isHorizontal mate) := by
    ext u
    simp only [allH, rowColour, mem_filter, mem_univ, true_and, and_comm]
    rw [show (¬ u.1.val % 2 = 0) ↔ u.1.val % 2 = 1 by omega]
  have hs := Finset.card_filter_add_card_filter_not (s := allH)
    (fun u => u.1.val % 2 = 0)
  rw [hh0, hh1] at hs
  have hh : allH.card = 0 ∨ allH.card = 4 := by omega
  rcases hh with hh | hh
  · left
    intro u
    have hempty := Finset.card_eq_zero.mp hh
    have hn : (mate u).1.val ≠ u.1.val := by
      intro h
      have hu : u ∈ allH := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.ext h⟩
      rw [hempty] at hu
      exact Finset.notMem_empty _ hu
    have h := hrow u
    unfold Nat.dist at *
    omega
  · right
    intro u
    have heq := Finset.eq_of_subset_of_card_le hsubset (by omega)
    have hn : (mate u).2.val ≠ u.2.val := by
      intro h
      have hu : u ∈ ordinaryCells mate := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Fin.ext h)⟩
      rw [← heq] at hu
      exact hfix u (Prod.ext (Finset.mem_filter.mp hu).2 (Fin.ext h))
    have h := hcol u
    unfold Nat.dist at *
    omega

/-- A row-partner permutation in a row pair with only vertical and diagonal moves. -/
abbrev RowMatching (n : ℕ) :=
  {f : Fin (2*n) → Fin (2*n) // Function.Involutive f ∧ ∀ c, Nat.dist (f c).val c.val ≤ 1}

/-- A tiling using vertical and diagonal moves only. -/
abbrev CrossRow (n : ℕ) :=
  {mate : Cell n → Cell n // Function.Involutive mate ∧ ∀ u,
    Nat.dist (mate u).1.val u.1.val = 1 ∧ Nat.dist (mate u).2.val u.2.val ≤ 1}

private def rowIndex {n : ℕ} (r : Fin (2*n)) : Fin n :=
  ⟨r.val / 2, by have := r.isLt; omega⟩

private theorem rowIndex_even {n j : ℕ} (hj : j < n) :
    rowIndex (evenRow hj) = ⟨j,hj⟩ := by
  apply Fin.ext
  change (2*j) / 2 = j
  omega

private theorem rowIndex_odd {n j : ℕ} (hj : j < n) :
    rowIndex (oddRow hj) = ⟨j,hj⟩ := by
  apply Fin.ext
  change (2*j+1) / 2 = j
  omega

private theorem rowIndex_flip {n : ℕ} (r : Fin (2*n)) : rowIndex (flip r) = rowIndex r := by
  obtain ⟨j,hj, hr | hr⟩ := pair_coordinate r
  · rw [hr, flip_even, rowIndex_even, rowIndex_odd]
  · rw [hr, flip_odd, rowIndex_even, rowIndex_odd]

private def assemble {n : ℕ} (rows : Fin n → RowMatching n) : CrossRow n :=
  ⟨fun u => (flip u.1, (rows (rowIndex u.1)).val u.2),
    ⟨fun u => Prod.ext (flip_involutive u.1)
         (by change (rows (rowIndex (flip u.1))).val
              ((rows (rowIndex u.1)).val u.2) = u.2
             rw [rowIndex_flip]
             exact (rows (rowIndex u.1)).property.1 u.2),
     fun u => ⟨flip_step u.1, (rows (rowIndex u.1)).property.2 u.2⟩⟩⟩

private theorem cross_row_pair {n : ℕ} (m : CrossRow n) (j : Fin n) :
    (∀ c, (m.val (evenRow j.isLt,c)).1 = oddRow j.isLt) ∧
    (∀ c, (m.val (oddRow j.isLt,c)).1 = evenRow j.isLt) :=
  partners_share_row_pair m.val m.property.1 (fun u => (m.property.2 u).1) j.val j.isLt

private def extract {n : ℕ} (m : CrossRow n) (j : Fin n) : RowMatching n := by
  let f (c : Fin (2*n)) : Fin (2*n) := (m.val (evenRow j.isLt,c)).2
  have hp := (cross_row_pair m j).1
  have hstep (c : Fin (2*n)) : Nat.dist (f c).val c.val ≤ 1 :=
    (m.property.2 (evenRow j.isLt,c)).2
  have hi : Function.Injective f := by
    intro x y hxy
    have he : m.val (evenRow j.isLt,x) = m.val (evenRow j.isLt,y) :=
      Prod.ext ((hp x).trans (hp y).symm) hxy
    exact congrArg Prod.snd (m.property.1.injective he)
  exact ⟨f, near_permutation_involutive f hi hstep, hstep⟩

private theorem extract_assemble {n : ℕ} (rows : Fin n → RowMatching n) :
    extract (assemble rows) = rows := by
  funext j
  apply Subtype.ext
  funext c
  change (rows (rowIndex (evenRow j.isLt))).val c = (rows j).val c
  rw [rowIndex_even]

private theorem assemble_extract {n : ℕ} (m : CrossRow n) : assemble (extract m) = m := by
  apply Subtype.ext
  funext u
  obtain ⟨r,c⟩ := u
  obtain ⟨j,hj,hr | hr⟩ := pair_coordinate r
  · subst r
    apply Prod.ext
    · change flip (evenRow hj) = (m.val (evenRow hj,c)).1
      rw [flip_even]
      exact ((cross_row_pair m ⟨j,hj⟩).1 c).symm
    · change (extract m (rowIndex (evenRow hj))).val c = (m.val (evenRow hj,c)).2
      rw [rowIndex_even]
      rfl
  · subst r
    let c' := (m.val (oddRow hj,c)).2
    have hm : m.val (oddRow hj,c) = (evenRow hj,c') :=
      Prod.ext ((cross_row_pair m ⟨j,hj⟩).2 c) rfl
    have hinv := m.property.1 (oddRow hj,c)
    rw [hm] at hinv
    apply Prod.ext
    · change flip (oddRow hj) = (m.val (oddRow hj,c)).1
      rw [flip_odd]
      exact ((cross_row_pair m ⟨j,hj⟩).2 c).symm
    · change (extract m (rowIndex (oddRow hj))).val c = c'
      rw [rowIndex_odd]
      have hc : (extract m ⟨j,hj⟩).val c' = c := congrArg Prod.snd hinv
      rw [← hc]
      exact (extract m ⟨j,hj⟩).property.1 c'

/-- A vertical-and-diagonal tiling is exactly one local permutation per row pair. -/
def verticalEquiv (n : ℕ) : CrossRow n ≃ (Fin n → RowMatching n) :=
  ⟨extract, assemble, assemble_extract, extract_assemble⟩

def fixedColumns {w : ℕ} (f : Fin w → Fin w) : Finset (Fin w) :=
  Finset.univ.filter fun c => f c = c

private theorem fixed_parity {w : ℕ} (f : Fin w → Fin w)
    (hinv : Function.Involutive f) : (fixedColumns f).card % 2 = w % 2 := by
  let upper : Finset (Fin w) := univ.filter fun v => v.val < (f v).val
  let lower : Finset (Fin w) := univ.filter fun v => (f v).val < v.val
  let moved : Finset (Fin w) := univ.filter fun v => f v ≠ v
  have hb : upper.card = lower.card := by
    let e : Fin w ≃ Fin w := ⟨f,f,hinv,hinv⟩
    apply Finset.card_equiv e
    intro v
    simp only [upper, lower, mem_filter, mem_univ, true_and]
    change v.val < (f v).val ↔ (f (f v)).val < (f v).val
    rw [hinv]
  have hu : moved.filter (fun v => v.val < (f v).val) = upper := by
    ext v
    simp only [moved, upper, mem_filter, mem_univ, true_and]
    exact ⟨And.right, fun h => ⟨fun he => by have hh := congrArg (fun x : Fin w => x.val) he; omega, h⟩⟩
  have hl : moved.filter (fun v => ¬ v.val < (f v).val) = lower := by
    ext v
    simp only [moved, lower, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hne,h⟩
      have hh : (f v).val ≠ v.val := fun e => hne (Fin.ext e)
      omega
    · intro h
      have hh : f v ≠ v := fun e => by have hh := congrArg (fun x : Fin w => x.val) e; omega
      exact ⟨hh, by omega⟩
  have hm := Finset.card_filter_add_card_filter_not (s := moved) (fun v => v.val < (f v).val)
  rw [hu,hl] at hm
  have hf := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin w))) (fun v => f v = v)
  change (fixedColumns f).card + moved.card = (univ : Finset (Fin w)).card at hf
  rw [Finset.card_univ, Fintype.card_fin] at hf
  omega

private def prefixMate {w : ℕ} (f : Fin w → Fin w) (v : Fin w)
    (hv : f v = v) (hi : Function.Injective f) (hstep : ∀ u, Nat.dist (f u).val u.val ≤ 1)
    (u : Fin v.val) : Fin v.val :=
  let x : Fin w := ⟨u.val, u.isLt.trans v.isLt⟩
  ⟨(f x).val, by
    have hx := u.isLt
    have hs := hstep x
    change Nat.dist (f x).val u.val ≤ 1 at hs
    have hne : (f x).val ≠ v.val := by
      intro h
      have he := hi ((Fin.ext h : f x = v).trans hv.symm)
      have he' : u.val = v.val := congrArg Fin.val he
      omega
    unfold Nat.dist at hs
    omega⟩

private theorem prefix_involutive {w : ℕ} (f : Fin w → Fin w) (v : Fin w)
    (hv : f v = v) (hinv : Function.Involutive f)
    (hstep : ∀ u, Nat.dist (f u).val u.val ≤ 1) :
    Function.Involutive (prefixMate f v hv hinv.injective hstep) := by
  intro u
  apply Fin.ext
  exact congrArg (fun x : Fin w => x.val) (hinv ⟨u.val, u.isLt.trans v.isLt⟩)

private theorem prefix_fixed_iff {w : ℕ} (f : Fin w → Fin w) (v : Fin w)
    (hv : f v = v) (hinv : Function.Involutive f)
    (hstep : ∀ u, Nat.dist (f u).val u.val ≤ 1) (u : Fin v.val) :
    prefixMate f v hv hinv.injective hstep u = u ↔
      f ⟨u.val, u.isLt.trans v.isLt⟩ = ⟨u.val, u.isLt.trans v.isLt⟩ := by
  constructor
  · intro h
    exact Fin.ext (congrArg (fun x : Fin v.val => x.val) h)
  · intro h
    exact Fin.ext (congrArg (fun x : Fin w => x.val) h)

theorem two_fixed_columns_parity {w : ℕ} (f : Fin w → Fin w)
    (hinv : Function.Involutive f) (hstep : ∀ u, Nat.dist (f u).val u.val ≤ 1)
    (a b : Fin w) (hab : a.val < b.val) (hfixed : fixedColumns f = {a,b}) :
    a.val % 2 = 0 ∧ b.val % 2 = 1 := by
  have ha : a ∈ fixedColumns f := by rw [hfixed]; simp
  have hb : b ∈ fixedColumns f := by rw [hfixed]; simp
  have hfa := (Finset.mem_filter.mp ha).2
  have hfb := (Finset.mem_filter.mp hb).2
  let fa := prefixMate f a hfa hinv.injective hstep
  let fb := prefixMate f b hfb hinv.injective hstep
  have ha0 : fixedColumns fa = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    let v : Fin w := ⟨u.val, u.isLt.trans a.isLt⟩
    have hv : v ∈ fixedColumns f :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (prefix_fixed_iff f a hfa hinv hstep u).1
        (Finset.mem_filter.mp hu).2⟩
    rw [hfixed, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · have hv' : u.val = a.val := congrArg Fin.val hv
      have := u.isLt
      omega
    · have hv' : u.val = b.val := congrArg Fin.val hv
      have := u.isLt
      omega
  have hb1 : fixedColumns fb = {⟨a.val,hab⟩} := by
    ext u
    simp only [fixedColumns, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    change prefixMate f b hfb hinv.injective hstep u = u ↔ u = ⟨a.val,hab⟩
    rw [prefix_fixed_iff f b hfb hinv hstep]
    constructor
    · intro hu
      let v : Fin w := ⟨u.val, u.isLt.trans b.isLt⟩
      have hv : v ∈ fixedColumns f := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
      rw [hfixed, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv | hv
      · exact Fin.ext (congrArg (fun x : Fin w => x.val) hv)
      · have hv' : u.val = b.val := congrArg Fin.val hv
        have := u.isLt
        omega
    · rintro rfl
      exact hfa
  have hpa := fixed_parity fa (prefix_involutive f a hfa hinv hstep)
  have hpb := fixed_parity fb (prefix_involutive f b hfb hinv hstep)
  rw [ha0, Finset.card_empty] at hpa
  rw [hb1, Finset.card_singleton] at hpb
  exact ⟨by omega, by omega⟩

/-- The fixed points determine a permutation made of neighboring transpositions. -/
theorem row_matching_ext {w : ℕ} (f g : Fin w → Fin w)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hfstep : ∀ u, Nat.dist (f u).val u.val ≤ 1)
    (hgstep : ∀ u, Nat.dist (g u).val u.val ≤ 1)
    (hfixed : ∀ u, f u = u ↔ g u = u) : f = g := by
  have main (k : ℕ) (hk : k < w) : f ⟨k,hk⟩ = g ⟨k,hk⟩ := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      let v : Fin w := ⟨k,hk⟩
      change f v = g v
      by_cases he : f v = v
      · exact he.trans ((hfixed v).1 he).symm
      by_cases hflo : (f v).val < k
      · have hp : f (f v) = g (f v) := ih (f v).val hflo (f v).isLt
        rw [hf] at hp
        have eq := hg (f v)
        rw [← hp] at eq
        exact eq.symm
      by_cases hglo : (g v).val < k
      · have hp : f (g v) = g (g v) := ih (g v).val hglo (g v).isLt
        rw [hg] at hp
        have eq := hf (g v)
        rw [hp] at eq
        exact eq
      have hfn : (f v).val ≠ k := fun h => he (Fin.ext h)
      have hgn : (g v).val ≠ k := fun h => he ((hfixed v).2 (Fin.ext h))
      have hfs := hfstep v
      have hgs := hgstep v
      unfold Nat.dist at hfs hgs
      change ((f v).val - k) + (k - (f v).val) ≤ 1 at hfs
      change ((g v).val - k) + (k - (g v).val) ≤ 1 at hgs
      exact Fin.ext (by omega)
  funext v
  exact main v.val v.isLt

private def moveWithFixed (a b v : ℕ) : ℕ :=
  if v = a ∨ v = b then v
  else if a < v ∧ v < b then
    if v % 2 = 0 then v - 1 else v + 1
  else if v % 2 = 0 then v + 1 else v - 1

private theorem move_bound {n a b v : ℕ} (hb : b < 2*n) (hv : v < 2*n) :
    moveWithFixed a b v < 2*n := by
  unfold moveWithFixed
  split_ifs <;> omega

private theorem move_inverse {a b v : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 1) (hab : a < b) :
    moveWithFixed a b (moveWithFixed a b v) = v := by
  unfold moveWithFixed
  split_ifs <;> omega

private theorem move_dist {a b v : ℕ} : Nat.dist (moveWithFixed a b v) v ≤ 1 := by
  unfold moveWithFixed Nat.dist
  split_ifs <;> omega

private theorem move_fixed {a b v : ℕ} :
    moveWithFixed a b v = v ↔ v = a ∨ v = b := by
  unfold moveWithFixed
  split_ifs <;> omega

private def withFixedPair {n : ℕ} (a b : Fin (2*n))
    (ha : a.val % 2 = 0) (hb : b.val % 2 = 1) (hab : a.val < b.val) : RowMatching n :=
  ⟨fun c => ⟨moveWithFixed a.val b.val c.val, move_bound b.isLt c.isLt⟩,
    ⟨fun _ => Fin.ext (move_inverse ha hb hab), fun _ => move_dist⟩⟩

private theorem withFixedPair_columns {n : ℕ} (a b : Fin (2*n))
    (ha : a.val % 2 = 0) (hb : b.val % 2 = 1) (hab : a.val < b.val) :
    fixedColumns (withFixedPair a b ha hb hab).val = {a,b} := by
  ext c
  simp only [fixedColumns, mem_filter, mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Fin.ext_iff]
  exact move_fixed

abbrev OrderedPair (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}
abbrev TwoFixedRow (n : ℕ) := {f : RowMatching n // (fixedColumns f.val).card = 2}

private def pairRow {n : ℕ} (p : OrderedPair n) : TwoFixedRow n := by
  let a := evenRow p.val.1.isLt
  let b := oddRow p.val.2.isLt
  have ha : a.val % 2 = 0 := by change (2 * p.val.1.val) % 2 = 0; omega
  have hb : b.val % 2 = 1 := by change (2 * p.val.2.val + 1) % 2 = 1; omega
  have hab : a.val < b.val := by
    have hp : p.val.1.val ≤ p.val.2.val := p.property
    change 2 * p.val.1.val < 2 * p.val.2.val + 1
    omega
  refine ⟨withFixedPair a b ha hb hab, ?_⟩
  rw [withFixedPair_columns]
  exact (Finset.card_eq_two.mpr ⟨a,b,fun e => by rw [e,hb] at ha; omega,rfl⟩)

private theorem pairRow_columns {n : ℕ} (p : OrderedPair n) :
    fixedColumns (pairRow p).val.val = {evenRow p.val.1.isLt, oddRow p.val.2.isLt} :=
  by simp only [pairRow, withFixedPair_columns]

private theorem pairRow_injective {n : ℕ} : Function.Injective (pairRow (n := n)) := by
  intro p q hpq
  have hs := congrArg (fun f : TwoFixedRow n => fixedColumns f.val.val) hpq
  rw [pairRow_columns, pairRow_columns] at hs
  have he : evenRow p.val.1.isLt ∈ ({evenRow q.val.1.isLt, oddRow q.val.2.isLt} : Finset (Fin (2*n))) := by
    rw [← hs]
    simp
  have ho : oddRow p.val.2.isLt ∈ ({evenRow q.val.1.isLt, oddRow q.val.2.isLt} : Finset (Fin (2*n))) := by
    rw [← hs]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at he ho
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · rcases he with he | he
    · have h : 2 * p.val.1.val = 2 * q.val.1.val := congrArg (fun x : Fin (2*n) => x.val) he
      omega
    · have h : 2 * p.val.1.val = 2 * q.val.2.val + 1 := congrArg (fun x : Fin (2*n) => x.val) he
      omega
  · rcases ho with ho | ho
    · have h : 2 * p.val.2.val + 1 = 2 * q.val.1.val := congrArg (fun x : Fin (2*n) => x.val) ho
      omega
    · have h : 2 * p.val.2.val + 1 = 2 * q.val.2.val + 1 := congrArg (fun x : Fin (2*n) => x.val) ho
      omega

private theorem sorted_fixed_columns {w : ℕ} (f : Fin w → Fin w)
    (hf : (fixedColumns f).card = 2) :
    ∃ a b : Fin w, a.val < b.val ∧ fixedColumns f = {a,b} := by
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp hf
  rcases lt_or_gt_of_ne (fun h : a.val = b.val => hab (Fin.ext h)) with h | h
  · exact ⟨a,b,h,he⟩
  · exact ⟨b,a,h,by rw [he,Finset.pair_comm]⟩

private theorem pairRow_surjective {n : ℕ} : Function.Surjective (pairRow (n := n)) := by
  intro f
  obtain ⟨a,b,hab,hs⟩ := sorted_fixed_columns f.val.val f.property
  obtain ⟨ha,hb⟩ := two_fixed_columns_parity f.val.val f.val.property.1 f.val.property.2 a b hab hs
  have hai := a.isLt
  have hbi := b.isLt
  let p : OrderedPair n :=
    ⟨(⟨a.val/2,by omega⟩,⟨b.val/2,by omega⟩), by change a.val/2 ≤ b.val/2; omega⟩
  have he : evenRow p.val.1.isLt = a := by
    apply Fin.ext
    change 2 * (a.val/2) = a.val
    omega
  have ho : oddRow p.val.2.isLt = b := by
    apply Fin.ext
    change 2 * (b.val/2) + 1 = b.val
    omega
  have hsame : fixedColumns (pairRow p).val.val = fixedColumns f.val.val := by
    rw [pairRow_columns, he, ho, hs]
  refine ⟨p, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply row_matching_ext _ _ (pairRow p).val.property.1 f.val.property.1
    (pairRow p).val.property.2 f.val.property.2
  intro u
  have h := congrArg (fun s : Finset (Fin (2*n)) => u ∈ s) hsame
  simpa [fixedColumns] using Iff.of_eq h

/-- The two fixed columns are exactly a weakly ordered pair of half-indices. -/
noncomputable def twoFixedEquiv (n : ℕ) : OrderedPair n ≃ TwoFixedRow n :=
  Equiv.ofBijective pairRow ⟨pairRow_injective, pairRow_surjective⟩

def fixedEntries {n : ℕ} (rows : Fin n → RowMatching n) : Finset (Fin n × Fin (2*n)) :=
  univ.filter fun p => (rows p.1).val p.2 = p.2

private theorem mem_fixedEntries {n : ℕ} {rows : Fin n → RowMatching n} (j : Fin n) (c : Fin (2*n)) :
    (j,c) ∈ fixedEntries rows ↔ c ∈ fixedColumns (rows j).val := by
  simp [fixedEntries, fixedColumns]

private def rowCoordinates (n : ℕ) : Cell n ≃ Fin 2 × (Fin n × Fin (2*n)) where
  toFun u := (⟨u.1.val%2, by omega⟩, (rowIndex u.1,u.2))
  invFun p := (⟨2*p.2.1.val+p.1.val, by
    have := p.1.isLt
    have := p.2.1.isLt
    omega⟩, p.2.2)
  left_inv u := Prod.ext (Fin.ext (by change 2*(u.1.val/2) + u.1.val%2 = u.1.val; omega)) rfl
  right_inv p := by
    obtain ⟨b,j,c⟩ := p
    have hb := b.isLt
    apply Prod.ext
    · apply Fin.ext
      change (2*j.val+b.val)%2 = b.val
      omega
    · apply Prod.ext
      · apply Fin.ext
        change (2*j.val+b.val)/2 = j.val
        omega
      · rfl

private theorem ordinary_assemble {n : ℕ} (rows : Fin n → RowMatching n) :
    (ordinaryCells (assemble rows).val).card = 2 * (fixedEntries rows).card := by
  have he : (ordinaryCells (assemble rows).val).card =
      ((univ : Finset (Fin 2)) ×ˢ fixedEntries rows).card := by
    apply Finset.card_equiv (rowCoordinates n)
    intro u
    simp only [ordinaryCells, fixedEntries, mem_filter, mem_univ, true_and,
      Finset.mem_product]
    change (flip u.1 = u.1 ∨ (rows (rowIndex u.1)).val u.2 = u.2) ↔
      (rows (rowIndex u.1)).val u.2 = u.2
    have hne : flip u.1 ≠ u.1 := by
      intro he
      have h := flip_step u.1
      rw [he, Nat.dist_self] at h
      omega
    simp only [hne, false_or]
  rw [he, Finset.card_product, Finset.card_univ, Fintype.card_fin]

private def transpositionsOnly (n : ℕ) : RowMatching n :=
  ⟨flip,flip_involutive,fun u => (flip_step u).le⟩

private theorem default_empty (n : ℕ) :
    fixedColumns (transpositionsOnly n).val = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hf : flip c = c := (Finset.mem_filter.mp hc).2
  have h := flip_step c
  rw [hf, Nat.dist_self] at h
  omega

private theorem eq_default_of_empty {n : ℕ} (f : RowMatching n)
    (hf : fixedColumns f.val = ∅) : f = transpositionsOnly n := by
  apply Subtype.ext
  apply row_matching_ext _ _ f.property.1 (transpositionsOnly n).property.1
    f.property.2 (transpositionsOnly n).property.2
  intro c
  have h := congrArg (fun s : Finset (Fin (2*n)) => c ∈ s) (hf.trans (default_empty n).symm)
  simpa [fixedColumns] using Iff.of_eq h

abbrev TwoFixedRows (n : ℕ) := {rows : Fin n → RowMatching n // (fixedEntries rows).card = 2}

private def selectFunction {n : ℕ} (p : Fin n × TwoFixedRow n) : Fin n → RowMatching n :=
  fun r => if r = p.1 then p.2.val else transpositionsOnly n

private theorem selected_entries {n : ℕ} (p : Fin n × TwoFixedRow n) :
    fixedEntries (selectFunction p) = ({p.1} : Finset (Fin n)) ×ˢ fixedColumns p.2.val.val := by
  ext x
  obtain ⟨j,c⟩ := x
  rw [mem_fixedEntries]
  by_cases hj : j = p.1
  · subst j
    rw [show selectFunction p p.1 = p.2.val by simp [selectFunction]]
    simp
  · rw [show selectFunction p j = transpositionsOnly n by simp [selectFunction, hj],
      default_empty]
    simp [Ne.symm hj]

private def selectRows {n : ℕ} (p : Fin n × TwoFixedRow n) : TwoFixedRows n :=
  ⟨selectFunction p, by rw [selected_entries, card_product, card_singleton, one_mul, p.2.property]⟩

private theorem select_injective {n : ℕ} : Function.Injective (selectRows (n := n)) := by
  intro p q he
  have hfun : selectFunction p = selectFunction q :=
    congrArg (fun r : TwoFixedRows n => r.val) he
  have hpq : p.1 = q.1 := by
    by_contra hne
    have he' := congrFun hfun p.1
    simp [selectFunction, hne] at he'
    have hc : fixedColumns p.2.val.val = fixedColumns (transpositionsOnly n).val :=
      congrArg (fun f : RowMatching n => fixedColumns f.val) he'
    rw [default_empty] at hc
    have := p.2.property
    rw [hc, card_empty] at this
    omega
  apply Prod.ext hpq
  apply Subtype.ext
  have h := congrFun hfun p.1
  simpa [selectFunction, hpq] using h

private theorem select_surjective {n : ℕ} : Function.Surjective (selectRows (n := n)) := by
  intro s
  obtain ⟨a,b,hne,hs⟩ := Finset.card_eq_two.mp s.property
  have hrow : a.1 = b.1 := by
    by_contra hh
    have hset : fixedColumns (s.val a.1).val = {a.2} := by
      ext c
      rw [← mem_fixedEntries (rows := s.val) a.1 c, hs]
      simp only [Finset.mem_insert, mem_singleton]
      constructor
      · intro he
        rcases he with he | he
        · exact congrArg Prod.snd he
        · have hproj := congrArg (fun p : Fin n × Fin (2*n) => p.1) he
          exact False.elim (hh hproj)
      · intro hc
        exact Or.inl (Prod.ext rfl hc)
    have hp := fixed_parity (s.val a.1).val (s.val a.1).property.1
    rw [hset, Finset.card_singleton] at hp
    omega
  have hset : fixedColumns (s.val a.1).val = {a.2,b.2} := by
    ext c
    rw [← mem_fixedEntries (rows := s.val) a.1 c, hs]
    simp only [Finset.mem_insert, mem_singleton]
    constructor
    · intro hh
      rcases hh with hh | hh
      · exact Or.inl (congrArg Prod.snd hh)
      · exact Or.inr (congrArg Prod.snd hh)
    · intro h
      rcases h with h | h
      · exact Or.inl (Prod.ext rfl h)
      · exact Or.inr (Prod.ext hrow h)
  have hf : (fixedColumns (s.val a.1).val).card = 2 := by
    rw [hset]
    exact Finset.card_eq_two.mpr ⟨a.2,b.2,fun hh => hne (Prod.ext hrow hh),rfl⟩
  refine ⟨(a.1, ⟨s.val a.1,hf⟩), ?_⟩
  apply Subtype.ext
  funext j
  change (if j = a.1 then s.val a.1 else transpositionsOnly n) = s.val j
  by_cases hj : j = a.1
  · rw [if_pos hj, hj]
  · rw [if_neg hj]
    symm
    apply eq_default_of_empty
    apply eq_empty_iff_forall_notMem.mpr
    intro c hc
    have he := (mem_fixedEntries (rows := s.val) j c).2 hc
    rw [hs, Finset.mem_insert, mem_singleton] at he
    rcases he with he | he
    · exact hj (congrArg Prod.fst he)
    · exact hj ((congrArg Prod.fst he).trans hrow.symm)

/-- Exactly one row pair has the two fixed columns. -/
noncomputable def selectedRowsEquiv (n : ℕ) : (Fin n × TwoFixedRow n) ≃ TwoFixedRows n :=
  Equiv.ofBijective selectRows ⟨select_injective,select_surjective⟩

abbrev TwoOrdinaryVertical (n : ℕ) := {m : CrossRow n // (ordinaryCells m.val).card = 4}

private def verticalWithTwoEquiv (n : ℕ) : TwoOrdinaryVertical n ≃ TwoFixedRows n where
  toFun m := ⟨extract m.val, by
    have eq := ordinary_assemble (extract m.val)
    rw [assemble_extract, m.property] at eq
    omega⟩
  invFun s := ⟨assemble s.val, by rw [ordinary_assemble, s.property]⟩
  left_inv m := Subtype.ext (assemble_extract m.val)
  right_inv s := Subtype.ext (extract_assemble s.val)

private def rowsCross {n : ℕ} (m : TwoOrdinary n) : Prop :=
  ∀ u, Nat.dist (m.val u).1.val u.1.val = 1

private def columnsCross {n : ℕ} (m : TwoOrdinary n) : Prop :=
  ∀ u, Nat.dist (m.val u).2.val u.2.val = 1

private def transposeMate {n : ℕ} (m : Cell n → Cell n) (u : Cell n) : Cell n :=
  (m u.swap).swap

private theorem transpose_cells {n : ℕ} (m : Cell n → Cell n) :
    (ordinaryCells (transposeMate m)).card = (ordinaryCells m).card := by
  apply Finset.card_equiv (Equiv.prodComm _ _)
  intro u
  simp only [ordinaryCells, mem_filter, mem_univ, true_and]
  change ((m u.swap).2 = u.1 ∨ (m u.swap).1 = u.2) ↔
    ((m u.swap).1 = u.2 ∨ (m u.swap).2 = u.1)
  exact or_comm

private def transpose {n : ℕ} (m : TwoOrdinary n) : TwoOrdinary n :=
  ⟨transposeMate m.val, ⟨fun u => by
      have h := congrArg Prod.swap (m.property.1 u.swap)
      simpa [transposeMate] using h,
    fun u h => by
      have hh := congrArg Prod.swap h
      exact (m.property.2.1 u.swap) (by simpa [transposeMate] using hh),
    fun u => m.property.2.2.2.1 u.swap,
    fun u => m.property.2.2.1 u.swap,
    by rw [transpose_cells, m.property.2.2.2.2]⟩⟩

private theorem transpose_involutive {n : ℕ} (m : TwoOrdinary n) :
    transpose (transpose m) = m := by
  apply Subtype.ext
  funext u
  change transposeMate (transposeMate m.val) u = m.val u
  simp [transposeMate]

private theorem transpose_rows {n : ℕ} (m : TwoOrdinary n) :
    rowsCross (transpose m) ↔ columnsCross m := by
  constructor
  · intro h u
    have hu := h u.swap
    simpa [transpose, transposeMate] using hu
  · intro h u
    exact h u.swap

private theorem transpose_columns {n : ℕ} (m : TwoOrdinary n) :
    columnsCross (transpose m) ↔ rowsCross m := by
  simpa only [transpose_involutive] using (transpose_rows (transpose m)).symm

private theorem not_both_axes {n : ℕ} (m : TwoOrdinary n) (hr : rowsCross m)
    (hc : columnsCross m) : False := by
  have hempty : ordinaryCells m.val = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    rcases (Finset.mem_filter.mp hu).2 with h | h
    · have hd := hr u
      rw [isHorizontal] at h
      rw [h, Nat.dist_self] at hd
      omega
    · have hd := hc u
      rw [isVertical] at h
      rw [h, Nat.dist_self] at hd
      omega
  have h := m.property.2.2.2.2
  rw [hempty, card_empty] at h
  omega

private def asVertical {n : ℕ} (m : TwoOrdinary n) (hr : rowsCross m) :
    TwoOrdinaryVertical n :=
  ⟨⟨m.val, ⟨m.property.1, fun u => ⟨hr u,m.property.2.2.2.1 u⟩⟩⟩,
    m.property.2.2.2.2⟩

private def ofVertical {n : ℕ} (m : TwoOrdinaryVertical n) : TwoOrdinary n :=
  ⟨m.val.val, ⟨m.val.property.1, fun u h => by
      have hd := (m.val.property.2 u).1
      rw [h, Nat.dist_self] at hd
      omega,
    fun u => (m.val.property.2 u).1.le,
    fun u => (m.val.property.2 u).2,
    m.property⟩⟩

private theorem rows_of_vertical {n : ℕ} (m : TwoOrdinaryVertical n) :
    rowsCross (ofVertical m) :=
  fun u => (m.val.property.2 u).1

private theorem to_vertical_back {n : ℕ} (m : TwoOrdinary n) (hr : rowsCross m) :
    ofVertical (asVertical m hr) = m := Subtype.ext rfl

private theorem from_vertical_back {n : ℕ} (m : TwoOrdinaryVertical n) :
    asVertical (ofVertical m) (rows_of_vertical m) = m := Subtype.ext (Subtype.ext rfl)

private noncomputable def orient {n : ℕ} (m : TwoOrdinary n) :
    TwoOrdinaryVertical n ⊕ TwoOrdinaryVertical n := by
  classical
  exact if h : rowsCross m then Sum.inl (asVertical m h)
    else Sum.inr (asVertical (transpose m) ((transpose_rows m).2
      ((two_ordinary_uniform m.val m.property.1 m.property.2.1
        m.property.2.2.1 m.property.2.2.2.1 m.property.2.2.2.2).resolve_left h)))

private def disorient {n : ℕ} : TwoOrdinaryVertical n ⊕ TwoOrdinaryVertical n → TwoOrdinary n
  | Sum.inl m => ofVertical m
  | Sum.inr m => transpose (ofVertical m)

private noncomputable def orientationEquiv (n : ℕ) :
    TwoOrdinary n ≃ (TwoOrdinaryVertical n ⊕ TwoOrdinaryVertical n) where
  toFun := orient
  invFun := disorient
  left_inv m := by
    classical
    unfold orient
    split_ifs with h
    · exact to_vertical_back m h
    · change transpose (ofVertical (asVertical (transpose m) _)) = m
      rw [to_vertical_back, transpose_involutive]
  right_inv q := by
    classical
    cases q with
    | inl m =>
        unfold disorient orient
        rw [dif_pos (rows_of_vertical m), from_vertical_back]
    | inr m =>
        have hc : columnsCross (transpose (ofVertical m)) :=
          (transpose_columns (ofVertical m)).2 (rows_of_vertical m)
        have hr : ¬ rowsCross (transpose (ofVertical m)) :=
          fun h => not_both_axes _ h hc
        unfold disorient orient
        rw [dif_neg hr]
        apply congrArg Sum.inr
        apply Subtype.ext
        apply Subtype.ext
        change (transpose (transpose (ofVertical m))).val = m.val.val
        rw [transpose_involutive]
        rfl

private abbrev StrictPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

private def orderEquiv (n : ℕ) : OrderedPair n ≃ StrictPair (n+1) where
  toFun p := ⟨(⟨p.val.1.val, p.val.1.isLt.trans (Nat.lt_succ_self n)⟩,
      ⟨p.val.2.val+1, Nat.succ_lt_succ p.val.2.isLt⟩), by
    have hh : p.val.1.val ≤ p.val.2.val := p.property
    exact Nat.lt_succ_of_le hh⟩
  invFun p := ⟨(⟨p.val.1.val, by
    have hp : p.val.1.val < p.val.2.val := p.property
    have hu := p.val.2.isLt
    omega⟩, ⟨p.val.2.val-1, by
    have hp : p.val.1.val < p.val.2.val := p.property
    have hu := p.val.2.isLt
    omega⟩), by
    have hp : p.val.1.val < p.val.2.val := p.property
    change p.val.1.val ≤ p.val.2.val - 1
    omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change p.val.2.val+1-1 = p.val.2.val
      omega
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      have hp : p.val.1.val < p.val.2.val := p.property
      change p.val.2.val-1+1 = p.val.2.val
      omega

private theorem ordered_pair_count (n : ℕ) :
    Fintype.card (OrderedPair n) = (n+1).choose 2 := by
  rw [Fintype.card_congr (orderEquiv n), Fintype.card_subtype]
  have h := Finset.card_product_filter_lt (s := (univ : Finset (Fin (n+1))))
  rw [Finset.card_univ, Fintype.card_fin] at h
  simpa using h

theorem nearCount_formula (n : ℕ) : nearCount n = n^2*(n+1) := by
  classical
  unfold nearCount
  let : Fintype (TwoOrdinary n) := Fintype.ofFinite _
  let : Fintype (TwoOrdinaryVertical n) := Fintype.ofFinite _
  let : Fintype (TwoFixedRows n) := Fintype.ofFinite _
  let : Fintype (TwoFixedRow n) := Fintype.ofFinite _
  have hvert : Fintype.card (TwoOrdinaryVertical n) = n * (n+1).choose 2 := by
    rw [Fintype.card_congr (verticalWithTwoEquiv n),
      ← Fintype.card_congr (selectedRowsEquiv n), Fintype.card_prod, Fintype.card_fin,
      ← Fintype.card_congr (twoFixedEquiv n), ordered_pair_count]
  rw [Fintype.card_congr (orientationEquiv n), Fintype.card_sum, hvert]
  have hd : 2 ∣ (n+1)*n := by
    have he : 2 ∣ n ∨ 2 ∣ n+1 := by omega
    rcases he with he | he
    · exact dvd_mul_of_dvd_right he (n+1)
    · exact dvd_mul_of_dvd_left he n
  have hdiv := Nat.div_mul_cancel hd
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  calc
    _ = n * (((n+1)*n/2)*2) := by ring
    _ = n^2*(n+1) := by rw [hdiv]; ring

end OpenMath.A401673

theorem OMA.solution : type_of% @OMA.S_oeis_a401673.main :=
  ⟨OpenMath.A401673.diagonalCount_one, fun n _ => OpenMath.A401673.nearCount_formula n⟩
