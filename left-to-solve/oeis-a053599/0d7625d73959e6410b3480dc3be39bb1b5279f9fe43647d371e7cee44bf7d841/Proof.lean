import OMAStatements.S_oeis_a053599
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

namespace OpenMath.A053599

open Finset

open OMA.S_oeis_a053599 (pal raised aset bset a b)

private abbrev Packet := Σ _ : ℕ, Σ _ : ℕ, Finset ℕ

private def bm (m L : ℕ) := max m (L - m)

private def bpackets (N : ℕ) : Finset Packet :=
  (Icc 2 N).sigma fun L => (Ioo 0 L).sigma fun m => (Ioo (bm m L) L).powerset

private def bbuild : Packet → Finset ℕ
  | ⟨L, m, U⟩ => insert m (insert L U)

private theorem bpacket_bounds {m L x : ℕ} {U : Finset ℕ}
    (hU : U ⊆ Ioo (bm m L) L) (hx : x ∈ U) :
    m < x ∧ x < L ∧ L < m + x := by
  obtain ⟨hl, hu⟩ := mem_Ioo.mp (hU hx)
  unfold bm at hl
  have hml := le_max_left m (L - m)
  have hmr := le_max_right m (L - m)
  omega

private theorem bbuild_mem {m L : ℕ} {U : Finset ℕ} (hm0 : 0 < m) (hml : m < L)
    (hU : U ⊆ Ioo (bm m L) L) {x : ℕ} (hx : x ∈ bbuild ⟨L, m, U⟩) :
    m ≤ x ∧ x ≤ L ∧ (m ≠ x → L < m + x) := by
  simp only [bbuild, mem_insert] at hx
  rcases hx with rfl | rfl | hu
  · omega
  · omega
  · have := bpacket_bounds hU hu
    omega

private theorem bbuild_valid (N : ℕ) :
    Set.MapsTo bbuild (bpackets N : Set Packet) (bset N : Set (Finset ℕ)) := by
  classical
  rintro ⟨L,m,U⟩ hz
  have hz' : L ∈ Icc 2 N ∧ m ∈ Ioo 0 L ∧ U ⊆ Ioo (bm m L) L := by
    simpa only [mem_coe, bpackets, mem_sigma, mem_powerset] using hz
  obtain ⟨hL, hm, hU⟩ := hz'
  obtain ⟨_, hLN⟩ := mem_Icc.mp hL
  obtain ⟨hm0, hmL⟩ := mem_Ioo.mp hm
  change bbuild ⟨L,m,U⟩ ∈ bset N
  rw [bset, mem_filter, mem_powerset]
  refine ⟨?_, ⟨m, by simp [bbuild], L, by simp [bbuild], hmL, ?_⟩⟩
  · intro x hx
    have h := bbuild_mem hm0 hmL hU hx
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro x hx
    exact bbuild_mem hm0 hmL hU hx

private theorem bbuild_inj (N : ℕ) :
    (bpackets N : Set Packet).InjOn bbuild := by
  classical
  rintro ⟨L,m,U⟩ hz ⟨L',m',U'⟩ hz' he
  have hpack {r s : ℕ} {T : Finset ℕ} (h : (⟨s,r,T⟩ : Packet) ∈ bpackets N) :
      0 < r ∧ r < s ∧ T ⊆ Ioo (bm r s) s := by
    simp only [bpackets, mem_sigma, mem_Icc, mem_Ioo, mem_powerset] at h
    exact ⟨h.2.1.1, h.2.1.2, h.2.2⟩
  have ⟨hm0,hml,hU⟩ := hpack hz
  have ⟨hm0',hml',hU'⟩ := hpack hz'
  have hm1 := (bbuild_mem hm0 hml hU (show m' ∈ bbuild ⟨L,m,U⟩ by rw [he]; simp [bbuild])).1
  have hm2 := (bbuild_mem hm0' hml' hU' (show m ∈ bbuild ⟨L',m',U'⟩ by rw [← he]; simp [bbuild])).1
  have hL1 := (bbuild_mem hm0 hml hU (show L' ∈ bbuild ⟨L,m,U⟩ by rw [he]; simp [bbuild])).2.1
  have hL2 := (bbuild_mem hm0' hml' hU' (show L ∈ bbuild ⟨L',m',U'⟩ by rw [← he]; simp [bbuild])).2.1
  have hmEq : m = m' := by omega
  have hLEq : L = L' := by omega
  subst m' L'
  obtain rfl : U = U' := by
    ext x
    constructor
    · intro hx
      have h := bpacket_bounds hU hx
      have h' : x ∈ bbuild ⟨L,m,U'⟩ := by rw [← he]; simp [bbuild, hx]
      simpa [bbuild, show x ≠ m by omega, show x ≠ L by omega] using h'
    · intro hx
      have h := bpacket_bounds hU' hx
      have h' : x ∈ bbuild ⟨L,m,U⟩ := by rw [he]; simp [bbuild, hx]
      simpa [bbuild, show x ≠ m by omega, show x ≠ L by omega] using h'
  rfl

private theorem bbuild_surj (N : ℕ) :
    Set.SurjOn bbuild (bpackets N : Set Packet) (bset N : Set (Finset ℕ)) := by
  classical
  intro S hs
  change S ∈ bset N at hs
  rw [bset, mem_filter, mem_powerset] at hs
  obtain ⟨hsub,m,hm,L,hL,hmL,hcond⟩ := hs
  let U := (S.erase m).erase L
  have hu : U ⊆ Ioo (bm m L) L := by
    intro x hx
    have hx' : x ≠ L ∧ x ≠ m ∧ x ∈ S := by simpa [U] using hx
    obtain ⟨hmx, hxL, hsum⟩ := hcond x hx'.2.2
    apply mem_Ioo.mpr
    unfold bm
    have hs' := hsum hx'.2.1.symm
    omega
  refine ⟨⟨L,m,U⟩, ?_, ?_⟩
  · change (⟨L,m,U⟩ : Packet) ∈ bpackets N
    have hmp := mem_Icc.mp (hsub hm)
    rw [bpackets]
    apply mem_sigma.mpr
    refine ⟨show L ∈ Icc 2 N from mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hsub hL)).2⟩, ?_⟩
    exact mem_sigma.mpr ⟨show m ∈ Ioo 0 L from mem_Ioo.mpr ⟨by omega, hmL⟩,
      mem_powerset.mpr hu⟩
  · ext x
    simp only [bbuild, mem_insert, U, mem_erase]
    grind

private theorem b_count (N : ℕ) :
    b N = ∑ L ∈ Icc 2 N, ∑ m ∈ Ioo 0 L, 2 ^ (L - bm m L - 1) := by
  have h := (card_nbij bbuild (bbuild_valid N) (bbuild_inj N) (bbuild_surj N)).symm
  simpa [b, bpackets, card_powerset, Nat.card_Ioo] using h

private def apackets (N : ℕ) : Finset Packet :=
  (Icc 1 N).sigma fun v => (Icc 1 v).sigma fun u => (Ioc u ((u + v) / 2)).powerset

private def abuild : Packet → Finset ℕ
  | ⟨v, u, U⟩ => insert u (insert v (U ∪ U.image (fun x => u + v - x)))

private theorem apacket {u v N : ℕ} {U : Finset ℕ} (h : (⟨v,u,U⟩ : Packet) ∈ apackets N) :
    (1 ≤ u ∧ u ≤ v) ∧ v ≤ N ∧ U ⊆ Ioc u ((u + v) / 2) := by
  simp only [apackets, mem_sigma, mem_Icc, mem_powerset] at h
  exact ⟨h.2.1, h.1.2, h.2.2⟩

private theorem abuild_bounds {u v : ℕ} {U : Finset ℕ} (huv : u ≤ v)
    (hU : U ⊆ Ioc u ((u + v) / 2)) {x : ℕ} (hx : x ∈ abuild ⟨v,u,U⟩) :
    u ≤ x ∧ x ≤ v ∧ u + v - x ∈ abuild ⟨v,u,U⟩ := by
  have he : x = u ∨ x = v ∨ x ∈ U ∨ ∃ y ∈ U, u + v - y = x := by
    simpa only [abuild, mem_insert, mem_union, mem_image] using hx
  rcases he with hxu | hxv | hx | ⟨y,hy,rfl⟩
  · subst x
    refine ⟨le_rfl, huv, ?_⟩
    simp [abuild, show u + v - u = v by omega]
  · subst x
    refine ⟨huv, le_rfl, ?_⟩
    simp [abuild, show u + v - v = u by omega]
  · have h := mem_Ioc.mp (hU hx)
    refine ⟨by omega, by omega, ?_⟩
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right U (mem_image_of_mem _ hx)))
  · have h := mem_Ioc.mp (hU hy)
    refine ⟨by omega, by omega, ?_⟩
    rw [show u + v - (u + v - y) = y by omega]
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ hy))

private theorem abuild_inside {u v : ℕ} {U : Finset ℕ} (huv : u ≤ v)
    (hU : U ⊆ Ioc u ((u + v) / 2)) {x : ℕ} (hx : x ∈ abuild ⟨v,u,U⟩)
    (hl : u < x) (hh : x ≤ (u + v) / 2) : x ∈ U := by
  have he : x = u ∨ x = v ∨ x ∈ U ∨ ∃ y ∈ U, u + v - y = x := by
    simpa only [abuild, mem_insert, mem_union, mem_image] using hx
  rcases he with rfl | rfl | h | ⟨y,hy,hxy⟩
  · omega
  · omega
  · exact h
  · have hy' := mem_Ioc.mp (hU hy)
    rwa [show x = y by omega]

private theorem abuild_valid (N : ℕ) :
    Set.MapsTo abuild (apackets N : Set Packet) (aset N : Set (Finset ℕ)) := by
  classical
  rintro ⟨v,u,U⟩ hp
  obtain ⟨⟨hu,huv⟩,hv,hU⟩ := apacket hp
  change abuild ⟨v,u,U⟩ ∈ aset N
  rw [aset, mem_filter, mem_powerset, pal]
  refine ⟨?_, ⟨u, by simp [abuild], v, by simp [abuild], ?_⟩⟩
  · intro x hx
    have h := abuild_bounds huv hU hx
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro x hx
    exact abuild_bounds huv hU hx


private theorem abuild_inj (N : ℕ) :
    (apackets N : Set Packet).InjOn abuild := by
  classical
  rintro ⟨v,u,U⟩ hz ⟨v',u',U'⟩ hz' he
  have ⟨⟨_,huv⟩,_,hU⟩ := apacket hz
  have ⟨⟨_,huv'⟩,_,hU'⟩ := apacket hz'
  have hu1 := (abuild_bounds huv hU (show u' ∈ abuild ⟨v,u,U⟩ by rw [he]; simp [abuild])).1
  have hu2 := (abuild_bounds huv' hU' (show u ∈ abuild ⟨v',u',U'⟩ by rw [← he]; simp [abuild])).1
  have hv1 := (abuild_bounds huv hU (show v' ∈ abuild ⟨v,u,U⟩ by rw [he]; simp [abuild])).2.1
  have hv2 := (abuild_bounds huv' hU' (show v ∈ abuild ⟨v',u',U'⟩ by rw [← he]; simp [abuild])).2.1
  have huEq : u = u' := by omega
  have hvEq : v = v' := by omega
  subst u' v'
  obtain rfl : U = U' := by
    ext x
    constructor
    · intro hx
      have ⟨hl,hh⟩ := mem_Ioc.mp (hU hx)
      have h' : x ∈ abuild ⟨v,u,U'⟩ := by rw [← he]; simp [abuild, hx]
      exact abuild_inside huv hU' h' hl hh
    · intro hx
      have ⟨hl,hh⟩ := mem_Ioc.mp (hU' hx)
      have h' : x ∈ abuild ⟨v,u,U⟩ := by rw [he]; simp [abuild, hx]
      exact abuild_inside huv hU h' hl hh
  rfl

private theorem abuild_surj (N : ℕ) :
    Set.SurjOn abuild (apackets N : Set Packet) (aset N : Set (Finset ℕ)) := by
  classical
  intro S hs
  change S ∈ aset N at hs
  rw [aset, mem_filter, mem_powerset] at hs
  obtain ⟨hsub,u,hu,v,hv,hcond⟩ := hs
  have huv := (hcond v hv).1
  let U := S.filter fun x => u < x ∧ x ≤ (u + v) / 2
  have hu' : U ⊆ Ioc u ((u + v) / 2) := by
    intro x hx
    exact mem_Ioc.mpr (mem_filter.mp hx).2
  refine ⟨⟨v,u,U⟩, ?_, ?_⟩
  · change (⟨v,u,U⟩ : Packet) ∈ apackets N
    rw [apackets]
    apply mem_sigma.mpr
    refine ⟨hsub hv, ?_⟩
    exact mem_sigma.mpr ⟨show u ∈ Icc 1 v from mem_Icc.mpr ⟨(mem_Icc.mp (hsub hu)).1, huv⟩,
      mem_powerset.mpr hu'⟩
  · ext x
    simp only [abuild, mem_insert, mem_union, mem_image, U, mem_filter]
    constructor
    · rintro (rfl | rfl | ⟨hx,_,_⟩ | ⟨y,⟨hy,_,_⟩,rfl⟩)
      · exact hu
      · exact hv
      · exact hx
      · exact (hcond y hy).2.2
    · intro hx
      by_cases hxu : x = u
      · exact Or.inl hxu
      by_cases hxv : x = v
      · exact Or.inr (Or.inl hxv)
      obtain ⟨hl,hh,hm⟩ := hcond x hx
      by_cases hsmall : x ≤ (u + v) / 2
      · exact Or.inr (Or.inr (Or.inl ⟨hx, by omega, hsmall⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨u + v - x, ⟨hm, by omega, by omega⟩, by omega⟩))

private theorem a_count (N : ℕ) :
    a N = ∑ v ∈ Icc 1 N, ∑ u ∈ Icc 1 v, 2 ^ ((v - u) / 2) := by
  have h := (card_nbij abuild (abuild_valid N) (abuild_inj N) (abuild_surj N)).symm
  rw [a, h, apackets, card_sigma]
  apply sum_congr rfl
  intro v _
  rw [card_sigma]
  apply sum_congr rfl
  intro u _
  rw [card_powerset, Nat.card_Ioc]
  congr 1
  omega

private def width (L m : ℕ) := if 2 * m ≤ L then 2 * (m - 1) else 2 * (L - m) - 1

private def fromWidth (L d : ℕ) :=
  if d % 2 = 0 then d / 2 + 1 else L - (d / 2 + 1)

private theorem width_bounds {L m : ℕ} (hm : m ∈ Ioo 0 L) :
    width L m ≤ L - 2 ∧ width L m / 2 = L - bm m L - 1 := by
  have h := mem_Ioo.mp hm
  by_cases hx : 2 * m ≤ L
  · have hmax : max m (L - m) = L - m := max_eq_right (by omega)
    simp only [width, if_pos hx, bm, hmax]
    omega
  · have hmax : max m (L - m) = m := max_eq_left (by omega)
    simp only [width, if_neg hx, bm, hmax]
    omega

private theorem width_left {L m : ℕ} (hm : m ∈ Ioo 0 L) :
    fromWidth L (width L m) = m := by
  have h := mem_Ioo.mp hm
  by_cases hx : 2 * m ≤ L
  · simp [width, hx, fromWidth]
    omega
  · have hd : (2 * (L - m) - 1) % 2 ≠ 0 := by omega
    simp only [width, if_neg hx, fromWidth, if_neg hd]
    omega

private theorem width_right {L d : ℕ} (hL : 2 ≤ L) (hd : d ≤ L - 2) :
    fromWidth L d ∈ Ioo 0 L ∧ width L (fromWidth L d) = d := by
  rw [mem_Ioo]
  by_cases hp : d % 2 = 0
  · have h2 : 2 * (d / 2 + 1) ≤ L := by omega
    simp only [fromWidth, if_pos hp, width, if_pos h2]
    omega
  · have h2 : ¬ 2 * (L - (d / 2 + 1)) ≤ L := by omega
    simp only [fromWidth, if_neg hp, width, if_neg h2]
    omega

private theorem inner (v : ℕ) (hv : 1 ≤ v) :
    (∑ m ∈ Ioo 0 (v + 1), (2 : ℕ) ^ (v + 1 - bm m (v + 1) - 1)) =
      ∑ u ∈ Icc 1 v, 2 ^ ((v - u) / 2) := by
  refine sum_nbij' (fun m => v - width (v + 1) m) (fun u => fromWidth (v + 1) (v - u))
    ?_ ?_ ?_ ?_ ?_
  · intro m hm
    have h := (width_bounds hm).1
    apply mem_Icc.mpr
    omega
  · intro u hu
    have h := mem_Icc.mp hu
    exact (width_right (by omega) (by omega)).1
  · intro m hm
    have h := (width_bounds hm).1
    rw [show v - (v - width (v + 1) m) = width (v + 1) m by omega]
    exact width_left hm
  · intro u hu
    have h := mem_Icc.mp hu
    have h' := (width_right (L := v+1) (d := v-u) (by omega) (by omega)).2
    simp only [h']
    omega
  · intro m hm
    obtain ⟨hb,hc⟩ := width_bounds hm
    rw [show v - (v - width (v + 1) m) = width (v + 1) m by omega, hc]

private theorem shift (n : ℕ) : b (n + 2) = a (n + 1) := by
  rw [b_count, a_count]
  refine sum_nbij' (fun L => L - 1) (fun v => v + 1) ?_ ?_ ?_ ?_ ?_
  · intro L h
    simp only [mem_Icc] at h ⊢
    omega
  · intro v h
    simp only [mem_Icc] at h ⊢
    omega
  · intro L h
    simp only [mem_Icc] at h
    omega
  · intro v _
    omega
  · intro L h
    have hL := (mem_Icc.mp h).1
    have he := inner (L - 1) (by omega)
    rwa [show L - 1 + 1 = L by omega] at he

theorem main : b 0 = 0 ∧ b 1 = 0 ∧ ∀ n : ℕ, b (n + 2) = a (n + 1) := by
  refine ⟨?_, ?_, shift⟩
  · rw [b_count]
    norm_num
  · rw [b_count]
    norm_num

end OpenMath.A053599

theorem OMA.solution : type_of% @OMA.S_oeis_a053599.main :=
  OpenMath.A053599.main
