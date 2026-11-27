import OMAStatements.S_oeis_a272911
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace OpenMath.A272911

open OMA.S_oeis_a272911 (L Mem FProduct Consecutive)

private theorem ls (n : ℕ) : L (n+2) = L n + L (n+1) := rfl

private theorem lpos (n : ℕ) : 0 < L n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < 2
    · interval_cases n <;> decide
    obtain ⟨k,rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
    rw [ls]
    exact add_pos (ih k (by omega)) (ih (k+1) (by omega))

private theorem lnext_lt (a : ℕ) (ha : 1 ≤ a) : L a < L (a+1) := by
  obtain ⟨k,rfl⟩ : ∃ k, a = k+1 := ⟨a-1, by omega⟩
  change L (k+1) < L (k+2)
  rw [ls]
  have h := lpos k
  omega

private theorem lle {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : L a ≤ L b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact ih.trans (lnext_lt n (by omega)).le

private theorem lfar {a b : ℕ} (h : a+2 ≤ b) : L a < L b := by
  have h0 : L a < L (a+2) := by rw [ls]; have hp := lpos (a+1); omega
  exact h0.trans_le (lle (by omega) h)

private theorem prod_formula (i j : ℕ) (hij : i ≤ j) :
    L i * L j = L (i+j) + (-1 : ℤ)^i * L (j-i) := by
  induction i using Nat.strong_induction_on generalizing j with
  | h i ih =>
    by_cases hi : i < 2
    · interval_cases i
      · simp [L, two_mul]
      · have h : j-1+2=j+1 := by omega
        have hs := ls (j-1)
        rw [h, show j-1+1=j by omega] at hs
        norm_num [L]
        rw [Nat.add_comm 1 j]
        omega
    obtain ⟨k,rfl⟩ : ∃ k, i = k+2 := ⟨i-2, by omega⟩
    have h1 := ih k (by omega) j (by omega)
    have h2 := ih (k+1) (by omega) j (by omega)
    have hsum := ls (k+j)
    rw [show k+j+2=k+2+j by omega, show k+j+1=k+1+j by omega] at hsum
    have hdiff := ls (j-(k+2))
    rw [show j-(k+2)+2=j-k by omega, show j-(k+2)+1=j-(k+1) by omega] at hdiff
    rw [ls, add_mul, h1, h2, hsum]
    rw [show (-1 : ℤ) ^ (k+2) = (-1)^k by rw [pow_add]; norm_num,
      pow_succ (-1 : ℤ) k, hdiff]
    ring

private theorem ldiff (d : ℕ) :
    L (d+4) - L d = 5 * (Nat.fib (d+2) : ℤ) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : d < 2
    · interval_cases d <;> decide
    obtain ⟨k,rfl⟩ : ∃ k, d = k+2 := ⟨d-2, by omega⟩
    have h1 := ih k (by omega)
    have h2 := ih (k+1) (by omega)
    have hL0 := ls k
    have hL4 := ls (k+4)
    have hF : Nat.fib (k+4) = Nat.fib (k+2) + Nat.fib (k+3) := Nat.fib_add_two
    simp only [Nat.add_assoc, Nat.reduceAdd] at h2 hL4
    change L (k+6) - L (k+2) = 5 * (Nat.fib (k+4) : ℤ)
    rw [hL4, hL0, hF, Nat.cast_add]
    linarith only [h1,h2]

private def entry (s i : ℕ) : ℤ := L i * L (s-i)

private def block (s : ℕ) (x : ℤ) : Prop :=
  1 ≤ s ∧ (x = L s ∨ ∃ i : ℕ, 2 ≤ i ∧ 2*i ≤ s ∧ x = entry s i)

private theorem entry_formula (s i : ℕ) (hi : 2*i ≤ s) :
    entry s i = if i % 2 = 0 then L s + L (s-2*i) else L s - L (s-2*i) := by
  unfold entry
  rw [prod_formula i (s-i) (by omega), show i+(s-i)=s by omega,
    show s-i-i=s-2*i by omega]
  by_cases h : i % 2 = 0
  · have hi' : Even i := ⟨i/2, by omega⟩
    simp [h, hi'.neg_one_pow]
  · have hi' : Odd i := ⟨i/2, by omega⟩
    simp [h, hi'.neg_one_pow]
    ring

private theorem member_of_block {s : ℕ} {x : ℤ} (hx : block s x) : Mem x := by
  rcases hx with ⟨hs,rfl | ⟨i,hi,his,rfl⟩⟩
  · exact ⟨1,s,by decide,hs,by simp [L]⟩
  · exact ⟨i,s-i,by omega,by omega,rfl⟩

private theorem mem_block {x : ℤ} (hx : Mem x) : ∃ s, block s x := by
  obtain ⟨i,j,hi,hj,rfl⟩ := hx
  by_cases h : i ≤ j
  · by_cases h1 : i = 1
    · subst i
      exact ⟨j,hj,Or.inl (by simp [L])⟩
    · exact ⟨i+j,by omega,Or.inr ⟨i,by omega,by omega,by simp [entry]⟩⟩
  · by_cases h1 : j = 1
    · subst j
      exact ⟨i,hi,Or.inl (by simp [L])⟩
    · exact ⟨j+i,by omega,Or.inr ⟨j,by omega,by omega,by simp [entry, mul_comm]⟩⟩


private theorem entry_order (s i j : ℕ) (his : 2*i ≤ s) (hjs : 2*j ≤ s)
    (hpar : i%2 = j%2) (hij : i<j) :
    if i%2=0 then entry s j < entry s i else entry s i < entry s j := by
  have hl : L (s-2*j) < L (s-2*i) := lfar (by omega)
  rw [entry_formula s i his, entry_formula s j hjs, ←hpar]
  split
  next _ => omega
  next _ => omega

private theorem odd_below (s i : ℕ) (his : 2*i ≤ s) (hpar : i%2 ≠ 0) :
    entry s i < L s := by
  rw [entry_formula s i his, if_neg hpar]
  have h := lpos (s-2*i)
  omega

private theorem even_above (s i : ℕ) (his : 2*i ≤ s) (hpar : i%2 = 0) :
    L s < entry s i := by
  rw [entry_formula s i his, if_pos hpar]
  have h := lpos (s-2*i)
  omega

private def maxValue (s : ℕ) := if 4 ≤ s then entry s 2 else L s
private def minValue (s : ℕ) := if 6 ≤ s then entry s 3 else L s

private theorem max_mem {s : ℕ} (hs : 1 ≤ s) : block s (maxValue s) := by
  refine ⟨hs, ?_⟩
  unfold maxValue
  split
  next h => exact Or.inr ⟨2, by decide, h, rfl⟩
  next _ => exact Or.inl rfl

private theorem min_mem {s : ℕ} (hs : 1 ≤ s) : block s (minValue s) := by
  refine ⟨hs, ?_⟩
  unfold minValue
  split
  next h => exact Or.inr ⟨3, by decide, h, rfl⟩
  next _ => exact Or.inl rfl

private theorem max_bound {s : ℕ} {x : ℤ} (hx : block s x) : x ≤ maxValue s := by
  by_cases h : 4 ≤ s
  · have hC := even_above s 2 h (by decide)
    rw [maxValue, if_pos h]
    rcases hx.2 with rfl | ⟨i,hi,his,rfl⟩
    · exact hC.le
    by_cases hi2 : i=2
    · subst i
      exact le_rfl
    by_cases hip : i%2=0
    · have horder := entry_order s 2 i h his (by simpa using hip.symm) (by omega)
      norm_num at horder
      exact horder.le
    · exact (odd_below s i his hip).le.trans hC.le
  · rw [maxValue, if_neg h]
    rcases hx.2 with rfl | ⟨i,hi,his,_⟩
    · exact le_rfl
    · omega

private theorem min_bound {s : ℕ} {x : ℤ} (hx : block s x) : minValue s ≤ x := by
  by_cases h : 6 ≤ s
  · have hC := odd_below s 3 h (by decide)
    rw [minValue, if_pos h]
    rcases hx.2 with rfl | ⟨i,hi,his,rfl⟩
    · exact hC.le
    by_cases hi3 : i=3
    · subst i
      exact le_rfl
    by_cases hip : i%2=0
    · exact hC.le.trans (even_above s i his hip).le
    · have horder := entry_order s 3 i h his (by simp; omega) (by omega)
      norm_num at horder
      exact horder.le
  · rw [minValue, if_neg h]
    rcases hx.2 with rfl | ⟨i,hi,his,rfl⟩
    · exact le_rfl
    · have hi2 : i=2 := by omega
      subst i
      exact (even_above s 2 his (by decide)).le

private theorem block_separation {s : ℕ} (hs : 1 ≤ s) : maxValue s < minValue (s+1) := by
  by_cases h : 5 ≤ s
  · rw [maxValue, if_pos (by omega), minValue, if_pos (by omega)]
    have he : s+1-3=s-2 := by omega
    unfold entry
    rw [he]
    change 3 * L (s-2) < 4 * L (s-2)
    have hp := lpos (s-2)
    omega
  · interval_cases s <;> decide

private theorem min_mono {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) : minValue s ≤ minValue t := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t ht ih =>
    have h0 : minValue t ≤ maxValue t := max_bound (min_mem (by omega))
    have h1 : maxValue t < minValue (t+1) := block_separation (by omega)
    exact ih.trans (h0.trans h1.le)

private theorem ordered_blocks {s t : ℕ} {x y : ℤ}
    (hx : block s x) (hy : block t y) (hst : s < t) : x < y := by
  have h0 : x ≤ maxValue s := max_bound hx
  have h1 : maxValue s < minValue (s+1) := block_separation hx.1
  have h2 : minValue (s+1) ≤ minValue t := min_mono (by omega) (by omega)
  have h3 : minValue t ≤ y := min_bound hy
  omega

private theorem lucas_gap (d : ℕ) : Mem (L d) ∨ FProduct (L d) := by
  by_cases h : 1 ≤ d
  · exact Or.inl ⟨1,d,by decide,h,by simp [L]⟩
  · have hd : d=0 := by omega
    subst d
    exact Or.inr ⟨1,3,by decide,by decide,by decide⟩

private theorem step_gap (s i : ℕ) (his : 2*(i+2) ≤ s) :
    if i%2=0 then entry s i - entry s (i+2) = 5 * (Nat.fib (s-2*i-2) : ℤ)
    else entry s (i+2) - entry s i = 5 * (Nat.fib (s-2*i-2) : ℤ) := by
  have hi : 2*i ≤ s := by omega
  have hf := ldiff (s-2*(i+2))
  rw [show s-2*(i+2)+4=s-2*i by omega,
    show s-2*(i+2)+2=s-2*i-2 by omega] at hf
  rw [entry_formula s i hi, entry_formula s (i+2) his, show (i+2)%2=i%2 by omega]
  split
  next _ => omega
  next _ => omega

private theorem fib_gap (i : ℕ) (hi : 1 ≤ i) : FProduct (5 * (Nat.fib i : ℤ)) :=
  ⟨5,i,by decide,hi,rfl⟩


private theorem even_gap {s i j : ℕ} (his : 2*i ≤ s) (hjs : 2*j ≤ s)
    (hip : i%2=0) (hjp : j%2=0) (hc : Consecutive (entry s i) (entry s j)) :
    FProduct (entry s j - entry s i) := by
  have hji : j<i := by
    by_contra! hh
    have hp := hc.1
    by_cases he : i=j
    · subst j
      omega
    · have hIn := entry_order s i j his hjs (hip.trans hjp.symm) (by omega)
      simp only [if_pos hip] at hIn
      omega
  have h2 : j+2 ≤ i := by omega
  have hj2 : i=j+2 := by
    by_contra hn
    have hz : Mem (entry s (j+2)) :=
      member_of_block ⟨by omega,Or.inr ⟨j+2,by omega,by omega,rfl⟩⟩
    have hl := entry_order s (j+2) i (by omega) his (by omega) (by omega)
    have hu := entry_order s j (j+2) hjs (by omega) (by omega) (by omega)
    have hjp2 : (j+2)%2=0 := by omega
    simp only [if_pos hjp2] at hl
    simp only [if_pos hjp] at hu
    exact hc.2.2.2 _ hl hu hz
  subst i
  have hd := step_gap s j his
  simp only [if_pos hjp] at hd
  rw [hd]
  exact fib_gap _ (by omega)

private theorem odd_gap {s i j : ℕ} (his : 2*i ≤ s) (hjs : 2*j ≤ s)
    (hip : i%2≠0) (hjp : j%2≠0) (hc : Consecutive (entry s i) (entry s j)) :
    FProduct (entry s j - entry s i) := by
  have hij : i<j := by
    by_contra! hh
    have hp := hc.1
    by_cases he : i=j
    · subst j
      omega
    · have hIn := entry_order s j i hjs his (by omega) (by omega)
      simp only [if_neg hjp] at hIn
      omega
  have h2 : i+2 ≤ j := by omega
  have hi2 : j=i+2 := by
    by_contra hn
    have hz : Mem (entry s (i+2)) :=
      member_of_block ⟨by omega,Or.inr ⟨i+2,by omega,by omega,rfl⟩⟩
    have hl := entry_order s i (i+2) his (by omega) (by omega) (by omega)
    have hu := entry_order s (i+2) j (by omega) hjs (by omega) (by omega)
    have hip2 : (i+2)%2≠0 := by omega
    simp only [if_neg hip] at hl
    simp only [if_neg hip2] at hu
    exact hc.2.2.2 _ hl hu hz
  subst j
  have hd := step_gap s i hjs
  simp only [if_neg hip] at hd
  rw [hd]
  exact fib_gap _ (by omega)

private theorem same_block_gap {s : ℕ} {x y : ℤ} (hx : block s x) (hy : block s y)
    (hc : Consecutive x y) : Mem (y-x) ∨ FProduct (y-x) := by
  have hs := hx.1
  rcases hx.2 with rfl | ⟨i,hi,his,rfl⟩
  · rcases hy.2 with rfl | ⟨j,hj,hjs,rfl⟩
    · have h := hc.1
      omega
    · by_cases hjp : j%2=0
      · rw [entry_formula s j hjs,if_pos hjp,add_sub_cancel_left]
        exact lucas_gap (s-2*j)
      · have h := odd_below s j hjs hjp
        have h' := hc.1
        omega
  · rcases hy.2 with rfl | ⟨j,hj,hjs,rfl⟩
    · by_cases hip : i%2=0
      · have h := even_above s i his hip
        have h' := hc.1
        omega
      · rw [entry_formula s i his,if_neg hip,sub_sub_cancel]
        exact lucas_gap (s-2*i)
    · by_cases hip : i%2=0
      · by_cases hjp : j%2=0
        · exact Or.inr (even_gap his hjs hip hjp hc)
        · have h1 := even_above s i his hip
          have h2 := odd_below s j hjs hjp
          have h := hc.1
          omega
      · by_cases hjp : j%2=0
        · have h1 := odd_below s i his hip
          have h2 := even_above s j hjs hjp
          exact (hc.2.2.2 (L s) h1 h2 (member_of_block ⟨hs,Or.inl rfl⟩)).elim
        · exact Or.inr (odd_gap his hjs hip hjp hc)

private theorem across_gap {s : ℕ} (hs : 1 ≤ s) :
    Mem (minValue (s+1)-maxValue s) ∨ FProduct (minValue (s+1)-maxValue s) := by
  by_cases h : 5 ≤ s
  · rw [minValue,if_pos (by omega),maxValue,if_pos (by omega)]
    unfold entry
    rw [show s+1-3=s-2 by omega]
    change Mem (4 * L (s-2) - 3 * L (s-2)) ∨ FProduct (4 * L (s-2) - 3 * L (s-2))
    rw [show 4 * L (s-2) - 3 * L (s-2) = L (s-2) by ring]
    exact lucas_gap (s-2)
  · interval_cases s
    · exact lucas_gap 0
    · exact lucas_gap 1
    · exact lucas_gap 2
    · exact lucas_gap 0

theorem main : ∀ x y : ℤ, Consecutive x y → Mem (y-x) ∨ FProduct (y-x) := by
  intro x y hc
  obtain ⟨s,hx⟩ := mem_block hc.2.1
  obtain ⟨t,hy⟩ := mem_block hc.2.2.1
  by_cases he : s=t
  · subst t
    exact same_block_gap hx hy hc
  have hst : s<t := by
    by_contra! h
    have h' := ordered_blocks hy hx (by omega)
    have hh := hc.1
    omega
  have ht : t=s+1 := by
    by_contra h
    have hz : block (s+1) (L (s+1)) := ⟨by omega,Or.inl rfl⟩
    exact hc.2.2.2 _ (ordered_blocks hx hz (by omega)) (ordered_blocks hz hy (by omega))
      (member_of_block hz)
  have hmax : x=maxValue s := by
    have hh := max_bound hx
    by_contra h
    have hz := max_mem hx.1
    exact hc.2.2.2 _ (by omega) (ordered_blocks hz hy hst) (member_of_block hz)
  have hmin : y=minValue t := by
    have hh := min_bound hy
    by_contra h
    have hz := min_mem hy.1
    exact hc.2.2.2 _ (ordered_blocks hx hz hst) (by omega) (member_of_block hz)
  rw [hmax,hmin,ht]
  exact across_gap hx.1

end OpenMath.A272911

theorem OMA.solution : type_of% @OMA.S_oeis_a272911.main :=
  OpenMath.A272911.main
