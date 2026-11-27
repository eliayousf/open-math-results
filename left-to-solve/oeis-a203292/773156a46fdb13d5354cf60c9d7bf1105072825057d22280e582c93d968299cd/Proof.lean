import OMAStatements.S_oeis_a203292
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace A203292Proof

open Finset

open OMA.S_oeis_a203292

private theorem mem_arrays {n : ℕ} {x y z t : ℤ} :
    (x,y,z,t) ∈ arrays n ↔ -(n : ℤ) ≤ x ∧ x ≤ y ∧ y ≤ z ∧ z ≤ t ∧
      t ≤ n ∧ x + y + z + t = 0 ∧ positiveCount (x,y,z,t) = negativeCount (x,y,z,t) := by
  simp only [arrays, mem_filter, mem_product, mem_Icc, good]
  constructor
  · rintro ⟨⟨⟨hlo,_⟩,_,_,⟨_,hhi⟩⟩,hxy,hyz,hzt,hs,hc⟩
    exact ⟨hlo,hxy,hyz,hzt,hhi,hs,hc⟩
  · rintro ⟨hlo,hxy,hyz,hzt,hhi,hs,hc⟩
    exact ⟨⟨⟨hlo, by omega⟩,⟨by omega, by omega⟩,⟨by omega, by omega⟩,
      ⟨by omega,hhi⟩⟩,hxy,hyz,hzt,hs,hc⟩

set_option maxHeartbeats 2000000 in
private theorem balanced_form {x y z t : ℤ} (hxy : x ≤ y) (hyz : y ≤ z) (hzt : z ≤ t)
    (hs : x + y + z + t = 0)
    (hc : positiveCount (x,y,z,t) = negativeCount (x,y,z,t)) :
    (x = 0 ∧ y = 0 ∧ z = 0 ∧ t = 0) ∨
    (x = -t ∧ y = 0 ∧ z = 0 ∧ 0 < t) ∨ (y < 0 ∧ 0 < z) := by
  simp only [positiveCount, negativeCount] at hc
  split_ifs at hc <;> omega

private def oneEmbedding : ℕ ↪ Quad :=
  ⟨fun u => (-(u : ℤ),0,0,(u : ℤ)), by
    intro u v h
    have := congrArg (fun q : Quad => q.2.2.2) h
    dsimp at this
    omega⟩

private def pairChoices (n s : ℕ) : Finset ℕ := Icc (max 1 (s - n)) (s / 2)

private def twoEmbedding : (Σ _ : ℕ, ℕ × ℕ) ↪ Quad :=
  ⟨fun ⟨s,x,y⟩ => ((x : ℤ) - s, -(x : ℤ), (y : ℤ), (s : ℤ) - y), by
    rintro ⟨s,x,y⟩ ⟨t,u,v⟩ h
    have hx := congrArg (fun q : Quad => q.2.1) h
    have hy := congrArg (fun q : Quad => q.2.2.1) h
    have hs := congrArg (fun q : Quad => q.1) h
    dsimp at hx hy hs
    have ex : x = u := by omega
    have ey : y = v := by omega
    have es : s = t := by omega
    subst u; subst v; subst t; rfl⟩

private def zeroFamily : Finset Quad := {(0,0,0,0)}
private def oneFamily (n : ℕ) : Finset Quad := (Icc 1 n).map oneEmbedding
private def twoFamily (n : ℕ) : Finset Quad :=
  ((Icc 2 (2*n)).sigma fun s => pairChoices n s ×ˢ pairChoices n s).map twoEmbedding

private theorem one_mem_arrays {n u : ℕ} (hu : u ∈ Icc 1 n) : oneEmbedding u ∈ arrays n := by
  rw [mem_Icc] at hu
  have hpos : 0 < (u : ℤ) := by omega
  have hneg : -(u : ℤ) < 0 := by omega
  have hnot1 : ¬ 0 < -(u : ℤ) := by omega
  have hnot2 : ¬ (u : ℤ) < 0 := by omega
  change (-(u : ℤ),0,0,(u : ℤ)) ∈ arrays n
  rw [mem_arrays]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  simp only [positiveCount, negativeCount, if_pos hpos, if_pos hneg,
    if_neg hnot1, if_neg hnot2, lt_irrefl, if_false]

private theorem two_mem_arrays {n s x y : ℕ} (hs : s ∈ Icc 2 (2*n))
    (hx : x ∈ pairChoices n s) (hy : y ∈ pairChoices n s) :
    twoEmbedding ⟨s,x,y⟩ ∈ arrays n := by
  simp only [pairChoices, mem_Icc, max_le_iff] at hs hx hy
  have hneg1 : (x : ℤ) - s < 0 := by omega
  have hneg2 : -(x : ℤ) < 0 := by omega
  have hpos3 : 0 < (y : ℤ) := by omega
  have hpos4 : 0 < (s : ℤ) - y := by omega
  have hnot1 : ¬ 0 < (x : ℤ) - s := by omega
  have hnot2 : ¬ 0 < -(x : ℤ) := by omega
  have hnot3 : ¬ (y : ℤ) < 0 := by omega
  have hnot4 : ¬ (s : ℤ) - y < 0 := by omega
  change ((x : ℤ)-s,-(x : ℤ),(y : ℤ),(s : ℤ)-y) ∈ arrays n
  rw [mem_arrays]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  simp only [positiveCount, negativeCount, if_pos hneg1, if_pos hneg2,
    if_pos hpos3, if_pos hpos4, if_neg hnot1, if_neg hnot2, if_neg hnot3, if_neg hnot4]

private theorem arrays_eq (n : ℕ) : arrays n = zeroFamily ∪ oneFamily n ∪ twoFamily n := by
  ext q
  rcases q with ⟨x,y,z,t⟩
  constructor
  · intro h
    obtain ⟨hlo,hxy,hyz,hzt,hhi,hs,hc⟩ := mem_arrays.mp h
    rcases balanced_form hxy hyz hzt hs hc with
      ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,hpos⟩ | ⟨hy,hz⟩
    · exact mem_union_left _ (mem_union_left _ (by simp [zeroFamily]))
    · apply mem_union_left _
      apply mem_union_right _
      refine mem_map.mpr ⟨t.toNat, ?_, ?_⟩
      · exact mem_Icc.mpr ⟨by omega, by omega⟩
      · change (-(t.toNat : ℤ),0,0,(t.toNat : ℤ)) = (-t,0,0,t)
        rw [Int.toNat_of_nonneg (show 0 ≤ t by omega)]
    · apply mem_union_right _
      let s := (z+t).toNat
      let u := (-y).toNat
      let v := z.toNat
      have es : (s : ℤ) = z+t := Int.toNat_of_nonneg (by omega)
      have eu : (u : ℤ) = -y := Int.toNat_of_nonneg (by omega)
      have ev : (v : ℤ) = z := Int.toNat_of_nonneg (by omega)
      refine mem_map.mpr ⟨⟨s,u,v⟩, ?_, ?_⟩
      · simp only [mem_sigma, mem_product, pairChoices, mem_Icc, max_le_iff]
        omega
      · change ((u : ℤ)-s,-(u : ℤ),(v : ℤ),(s : ℤ)-v) = (x,y,z,t)
        have h1 : -y - (z + t) = x := by omega
        have h4 : z + t - z = t := by omega
        rw [es, eu, ev, h1, neg_neg, h4]
  · intro h
    rcases mem_union.mp h with h | h
    · rcases mem_union.mp h with h | h
      · rw [zeroFamily, mem_singleton] at h
        cases h
        rw [mem_arrays]
        simp [positiveCount, negativeCount]
      · obtain ⟨u,hu,he⟩ := mem_map.mp h
        rw [← he]
        exact one_mem_arrays hu
    · obtain ⟨⟨s,u,v⟩,hmem,he⟩ := mem_map.mp h
      rw [← he]
      obtain ⟨hs,hu,hv⟩ := by simpa only [mem_sigma, mem_product] using hmem
      exact two_mem_arrays hs hu hv

private theorem one_fields {n : ℕ} {q : Quad} (h : q ∈ oneFamily n) :
    q.2.2.1 = 0 ∧ 0 < q.2.2.2 := by
  obtain ⟨u,hu,rfl⟩ := mem_map.mp h
  have := (mem_Icc.mp hu).1
  change (0 : ℤ) = 0 ∧ 0 < (u : ℤ)
  omega

private theorem two_field {n : ℕ} {q : Quad} (h : q ∈ twoFamily n) : 0 < q.2.2.1 := by
  obtain ⟨⟨s,u,v⟩,hmem,rfl⟩ := mem_map.mp h
  have hv := (mem_product.mp (mem_sigma.mp hmem).2).2
  have hv1 := (max_le_iff.mp (mem_Icc.mp hv).1).1
  change 1 ≤ v at hv1
  change 0 < (v : ℤ)
  omega

private theorem cardinal (n : ℕ) :
    a n = 1 + n + ∑ s ∈ Icc 2 (2*n), (pairChoices n s).card ^ 2 := by
  have hzo : Disjoint zeroFamily (oneFamily n) := by
    rw [Finset.disjoint_left]
    intro q hz ho
    have hfields := one_fields ho
    rw [zeroFamily, mem_singleton] at hz
    rw [hz] at hfields
    exact (lt_irrefl _) hfields.2
  have hzt : Disjoint (zeroFamily ∪ oneFamily n) (twoFamily n) := by
    rw [Finset.disjoint_left]
    intro q h htwo
    have ht := two_field htwo
    rcases mem_union.mp h with hz | ho
    · rw [zeroFamily, mem_singleton] at hz
      rw [hz] at ht
      exact (lt_irrefl _) ht
    · rw [(one_fields ho).1] at ht
      exact (lt_irrefl _) ht
  rw [a, arrays_eq, card_union_of_disjoint hzt, card_union_of_disjoint hzo]
  simp [zeroFamily, oneFamily, twoFamily, card_sigma, pow_two]

private theorem low_card {n s : ℕ} (hs : s ≤ n + 1) : (pairChoices n s).card = s / 2 := by
  rw [pairChoices, Nat.card_Icc, max_eq_left (by omega : s - n ≤ 1)]
  omega

private theorem high_card {n s : ℕ} (hs : n + 2 ≤ s) (ht : s ≤ 2 * n) :
    (pairChoices n s).card = (2 * n + 2 - s) / 2 := by
  rw [pairChoices, Nat.card_Icc, max_eq_right (by omega : 1 ≤ s - n)]
  omega

private theorem reflection (n : ℕ) :
    (∑ s ∈ Icc (n + 2) (2*n), (pairChoices n s).card ^ 2) =
      ∑ s ∈ Icc 2 n, (s / 2) ^ 2 := by
  apply sum_bij (fun s _ => 2*n+2-s)
  · intro s hs
    simp only [mem_Icc] at hs ⊢
    omega
  · intro s hs t ht he
    simp only [mem_Icc] at hs ht
    omega
  · intro s hs
    simp only [mem_Icc] at hs
    refine ⟨2*n+2-s, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro s hs
    obtain ⟨hs₁,hs₂⟩ := mem_Icc.mp hs
    rw [high_card hs₁ hs₂]

private def squares (n : ℕ) : ℕ := ∑ s ∈ range (n+1), (s/2)^2

private theorem squares_eq_interval (n : ℕ) : ∑ s ∈ Icc 2 n, (s/2)^2 = squares n := by
  unfold squares
  apply sum_subset
  · intro s hs
    simp only [mem_Icc, mem_range] at hs ⊢
    omega
  · intro s hs hnot
    simp only [mem_Icc, mem_range] at hs hnot
    have h : s < 2 := by omega
    interval_cases s <;> decide

private theorem count_formula (n : ℕ) (hn : 1 ≤ n) :
    a n = 1 + n + ((n+1)/2)^2 + 2 * squares n := by
  have hpartition : Icc 2 (2*n) = (Icc 2 n ∪ {n+1}) ∪ Icc (n+2) (2*n) := by
    ext s
    simp only [mem_union, mem_Icc, mem_singleton]
    omega
  have hdis₁ : Disjoint (Icc 2 n) {n+1} := by
    rw [Finset.disjoint_left]
    simp only [mem_Icc, mem_singleton]
    omega
  have hdis₂ : Disjoint (Icc 2 n ∪ {n+1}) (Icc (n+2) (2*n)) := by
    rw [Finset.disjoint_left]
    simp only [mem_union, mem_Icc, mem_singleton]
    omega
  have hl : (∑ s ∈ Icc 2 n, (pairChoices n s).card^2) = squares n := by
    rw [← squares_eq_interval]
    apply sum_congr rfl
    intro s hs
    rw [low_card (by have := (mem_Icc.mp hs).2; omega)]
  rw [cardinal, hpartition, sum_union hdis₂, sum_union hdis₁, sum_singleton, hl,
    reflection, squares_eq_interval, low_card (le_refl _)]
  omega

private theorem squares_succ (n : ℕ) : squares (n+1) = squares n + ((n+1)/2)^2 := by
  exact sum_range_succ _ (n+1)

private theorem squares_parity (m : ℕ) :
    3 * squares (2*m) = 2*m^3+m ∧ 3 * squares (2*m+1) = 2*m^3+3*m^2+m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have he : squares (2*(m+1)) = squares (2*m+1) + (m+1)^2 := by
      have h := squares_succ (2*m+1)
      rw [show (2*m+1+1)/2 = m+1 by omega, show 2*m+1+1 = 2*(m+1) by omega] at h
      exact h
    have ho : squares (2*(m+1)+1) = squares (2*(m+1)) + (m+1)^2 := by
      rw [squares_succ, show (2*(m+1)+1)/2 = m+1 by omega]
    constructor
    · rw [he, Nat.mul_add, ih.2]
      ring
    · rw [ho, he, Nat.mul_add, Nat.mul_add, ih.2]
      ring

theorem closed_even (n : ℕ) (hn : 1 ≤ n) (h : n % 2 = 0) :
    24 * a n = 24 + 32*n + 6*n^2 + 4*n^3 := by
  obtain ⟨m,rfl⟩ : ∃ m, n = 2*m := ⟨n/2, by omega⟩
  rw [count_formula _ hn, show (2*m+1)/2 = m by omega]
  calc
    _ = 24 + 48*m + 24*m^2 + 16*(3*squares (2*m)) := by ring
    _ = _ := by rw [(squares_parity m).1]; ring

theorem closed_odd (n : ℕ) (hn : 1 ≤ n) (h : n % 2 = 1) :
    24 * a n = 30 + 32*n + 6*n^2 + 4*n^3 := by
  obtain ⟨m,rfl⟩ : ∃ m, n = 2*m+1 := ⟨n/2, by omega⟩
  rw [count_formula _ hn, show (2*m+1+1)/2 = m+1 by omega]
  calc
    _ = 24*(1+(2*m+1)+(m+1)^2) + 16*(3*squares (2*m+1)) := by ring
    _ = _ := by rw [(squares_parity m).2]; ring

private theorem closed_scaled (n : ℕ) (hn : 1 ≤ n) :
    (24 : ℤ) * a n = (if n % 2 = 0 then 24 else 30) + 32*(n : ℤ) +
      6*(n : ℤ)^2 + 4*(n : ℤ)^3 := by
  by_cases he : n % 2 = 0
  · rw [if_pos he]
    exact_mod_cast closed_even n hn he
  · rw [if_neg he]
    exact_mod_cast closed_odd n hn (by omega)

theorem linear_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (a (n+5) : ℤ) - 3*a (n+4) + 2*a (n+3) + 2*a (n+2) - 3*a (n+1) + a n = 0 := by
  have h : (24 : ℤ) * ((a (n+5) : ℤ) - 3*a (n+4) + 2*a (n+3) + 2*a (n+2) -
      3*a (n+1) + a n) = 0 := by
    calc
      _ = (24 : ℤ)*a (n+5) - 3*(24*a (n+4)) + 2*(24*a (n+3)) + 2*(24*a (n+2)) -
          3*(24*a (n+1)) + 24*a n := by ring
      _ = 0 := by
        rw [closed_scaled (n+5) (by omega), closed_scaled (n+4) (by omega),
          closed_scaled (n+3) (by omega), closed_scaled (n+2) (by omega),
          closed_scaled (n+1) (by omega), closed_scaled n hn]
        push_cast
        by_cases he : n % 2 = 0
        · simp only [if_pos he, if_pos (show (n+2)%2=0 by omega),
            if_pos (show (n+4)%2=0 by omega), if_neg (show (n+1)%2≠0 by omega),
            if_neg (show (n+3)%2≠0 by omega), if_neg (show (n+5)%2≠0 by omega)]
          ring
        · simp only [if_neg he, if_neg (show (n+2)%2≠0 by omega),
            if_neg (show (n+4)%2≠0 by omega), if_pos (show (n+1)%2=0 by omega),
            if_pos (show (n+3)%2=0 by omega), if_pos (show (n+5)%2=0 by omega)]
          ring
  omega

private theorem initial_values : a 1 = 3 ∧ a 2 = 6 ∧ a 3 = 12 ∧ a 4 = 21 ∧ a 5 = 35 := by
  have h1 := closed_odd 1 (by decide) (by decide)
  have h2 := closed_even 2 (by decide) (by decide)
  have h3 := closed_odd 3 (by decide) (by decide)
  have h4 := closed_even 4 (by decide) (by decide)
  have h5 := closed_odd 5 (by decide) (by decide)
  norm_num at h1 h2 h3 h4 h5
  omega

open PowerSeries in
theorem generating_function :
    ((1 - X) ^ 4 * (1 + X) : ℤ⟦X⟧) * mk seriesCoeff =
      X * (3 - 3 * X + 3 * X ^ 3 - X ^ 4) := by
  have hden : ((1-X)^4 * (1+X) : ℤ⟦X⟧) =
      1 - C 3 * X^1 + C 2 * X^2 + C 2 * X^3 - C 3 * X^4 + X^5 := by
    simp only [map_ofNat]
    ring
  have hnum : (X * (3 - 3 * X + 3 * X^3 - X^4) : ℤ⟦X⟧) =
      C 3 * X^1 - C 3 * X^2 + C 3 * X^4 - X^5 := by
    simp only [map_ofNat]
    ring
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n ≤ 5
  · obtain ⟨h1,h2,h3,h4,h5⟩ := initial_values
    interval_cases n <;> norm_num [seriesCoeff, h1, h2, h3, h4, h5]
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 5 := ⟨n-5, by omega⟩
  simp only [if_pos (show 1 ≤ k+5 by omega), if_pos (show 2 ≤ k+5 by omega),
    if_pos (show 3 ≤ k+5 by omega), if_pos (show 4 ≤ k+5 by omega),
    if_pos (show 5 ≤ k+5 by omega), if_neg (show k+5≠1 by omega),
    if_neg (show k+5≠2 by omega), if_neg (show k+5≠4 by omega), if_neg (show k+5≠5 by omega)]
  change seriesCoeff (k+5) - 3*seriesCoeff (k+4) + 2*seriesCoeff (k+3) +
      2*seriesCoeff (k+2) - 3*seriesCoeff (k+1) + seriesCoeff k = _
  simp only [seriesCoeff, if_neg (show k+5≠0 by omega), if_neg (show k+4≠0 by omega),
    if_neg (show k+3≠0 by omega), if_neg (show k+2≠0 by omega), if_neg (show k+1≠0 by omega),
    if_neg (show k≠0 by omega)]
  have h := linear_recurrence k (by omega)
  omega

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 ≤ n → n % 2 = 0 → 24 * a n = 24 + 32*n + 6*n^2 + 4*n^3) ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 1 → 24 * a n = 30 + 32*n + 6*n^2 + 4*n^3) ∧
    (((1 - X)^4 * (1 + X) : ℤ⟦X⟧) * mk seriesCoeff =
      X * (3 - 3*X + 3*X^3 - X^4)) :=
  ⟨closed_even, closed_odd, generating_function⟩

end A203292Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a203292.main := A203292Proof.main
