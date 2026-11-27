import OMAStatements.S_oeis_a272917
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace OpenMath.A272917

open OMA.S_oeis_a272917 (L Mem FProduct Consecutive Both ConsecutiveBoth)

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

private abbrev F (n : ℕ) : ℤ := Nat.fib n

private theorem fs (n : ℕ) : F (n+2) = F n + F (n+1) := by
  exact_mod_cast (show Nat.fib (n+2)=Nat.fib n+Nat.fib (n+1) from Nat.fib_add_two)

private theorem fp (i : ℕ) (hi : 1 ≤ i) : 0 < F i := by
  exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < i)

private theorem l_fib (n : ℕ) : L (n+1) = F n + F (n+2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < 2
    · interval_cases n <;> decide
    obtain ⟨k,rfl⟩ : ∃ k, n=k+2 := ⟨n-2,by omega⟩
    have h1 := ih k (by omega)
    have h2 := ih (k+1) (by omega)
    have hL := ls (k+1)
    have hF := fs (k+2)
    have hF0 := fs k
    simp only [Nat.add_assoc,Nat.reduceAdd] at h2 hL hF ⊢
    linarith only [h1,h2,hL,hF,hF0]

private theorem five_F (j : ℕ) (hj : 1 ≤ j) : L (j+1)+L (j-1)=5*F j := by
  by_cases h : j=1
  · subst j
    decide
  obtain ⟨k,rfl⟩ : ∃ k, j=k+2 := ⟨j-2,by omega⟩
  change L (k+3)+L (k+2-1)=5*F (k+2)
  rw [show k+2-1=k+1 by omega, show k+3=k+2+1 by omega, l_fib, l_fib]
  have h1 := fs k
  have h2 := fs (k+1)
  have h3 := fs (k+2)
  simp only [Nat.add_assoc,Nat.reduceAdd] at h2 h3
  linarith

private theorem fib_prod_formula (i j : ℕ) (hij : i ≤ j) :
    5*(F i*F j) = L (i+j) - (-1 : ℤ)^i * L (j-i) := by
  induction i using Nat.strong_induction_on generalizing j with
  | h i ih =>
    by_cases hi : i < 2
    · interval_cases i
      · simp
      · have h := five_F j hij
        have h0 : F 1=1 := rfl
        rw [h0,one_mul]
        norm_num
        rw [Nat.add_comm 1 j]
        omega
    obtain ⟨k,rfl⟩ : ∃ k, i = k+2 := ⟨i-2, by omega⟩
    have h1 := ih k (by omega) j (by omega)
    have h2 := ih (k+1) (by omega) j (by omega)
    have hsum := ls (k+j)
    rw [show k+j+2=k+2+j by omega, show k+j+1=k+1+j by omega] at hsum
    have hdiff := ls (j-(k+2))
    rw [show j-(k+2)+2=j-k by omega, show j-(k+2)+1=j-(k+1) by omega] at hdiff
    rw [fs,add_mul,mul_add,h1,h2,hsum]
    rw [show (-1 : ℤ) ^ (k+2) = (-1)^k by rw [pow_add]; norm_num,
      pow_succ (-1 : ℤ) k, hdiff]
    ring

private def fentry (s i : ℕ) : ℤ := F i * F (s-i)
private def fblock (s : ℕ) (x : ℤ) : Prop :=
  4 ≤ s ∧ ∃ i : ℕ, 2 ≤ i ∧ 2*i ≤ s ∧ x = fentry s i

private theorem fentry_formula (s i : ℕ) (hi : 2*i ≤ s) :
    5*fentry s i = if i%2=0 then L s - L (s-2*i) else L s + L (s-2*i) := by
  unfold fentry
  rw [fib_prod_formula i (s-i) (by omega), show i+(s-i)=s by omega,
    show s-i-i=s-2*i by omega]
  by_cases h : i%2=0
  · have hi' : Even i := ⟨i/2, by omega⟩
    simp [h,hi'.neg_one_pow]
  · have hi' : Odd i := ⟨i/2, by omega⟩
    simp [h,hi'.neg_one_pow]

private theorem fmember_of_block {s : ℕ} {x : ℤ} (hx : fblock s x) : FProduct x := by
  obtain ⟨hs,i,hi,his,rfl⟩ := hx
  exact ⟨i,s-i,by omega,by omega,rfl⟩

private theorem fmem_block {x : ℤ} (hx : FProduct x) : ∃ s, fblock s x := by
  obtain ⟨i,j,hi,hj,he⟩ := hx
  let p := max i 2
  let q := max j 2
  have hF (m : ℕ) (hm : 1 ≤ m) : F (max m 2) = F m := by
    by_cases h : 2 ≤ m
    · rw [max_eq_left h]
    · have hm1 : m=1 := by omega
      subst m
      decide
  have he' : x = F p * F q := by rw [hF i hi,hF j hj]; exact he
  have hp : 2 ≤ p := le_max_right i 2
  have hq : 2 ≤ q := le_max_right j 2
  by_cases h : p ≤ q
  · exact ⟨p+q,by omega,p,hp,by omega,by simpa [fentry] using he'⟩
  · exact ⟨q+p,by omega,q,hq,by omega,by simpa [fentry,mul_comm] using he'⟩

private theorem fentry_order (s i j : ℕ) (his : 2*i ≤ s) (hjs : 2*j ≤ s)
    (hpar : i%2=j%2) (hij : i<j) :
    if i%2=0 then fentry s i < fentry s j else fentry s j < fentry s i := by
  have hl : L (s-2*j) < L (s-2*i) := lfar (by omega)
  have h1 := fentry_formula s i his
  have h2 := fentry_formula s j hjs
  rw [←hpar] at h2
  split
  next h =>
    simp only [if_pos h] at h1 h2
    omega
  next h =>
    simp only [if_neg h] at h1 h2
    omega

private theorem fbelow (s i : ℕ) (his : 2*i ≤ s) (hip : i%2=0) :
    5*fentry s i < L s := by
  rw [fentry_formula s i his,if_pos hip]
  have h := lpos (s-2*i)
  omega

private theorem fabove (s i : ℕ) (his : 2*i ≤ s) (hip : i%2≠0) :
    L s < 5*fentry s i := by
  rw [fentry_formula s i his,if_neg hip]
  have h := lpos (s-2*i)
  omega

private def fmin (s : ℕ) := fentry s 2
private def fmax (s : ℕ) := if 6 ≤ s then fentry s 3 else fentry s 2

private theorem fmin_mem {s : ℕ} (hs : 4 ≤ s) : fblock s (fmin s) :=
  ⟨hs,2,by decide,hs,rfl⟩

private theorem fmax_mem {s : ℕ} (hs : 4 ≤ s) : fblock s (fmax s) := by
  refine ⟨hs,?_⟩
  unfold fmax
  split
  next h => exact ⟨3,by decide,h,rfl⟩
  next _ => exact ⟨2,by decide,hs,rfl⟩

private theorem fmin_bound {s : ℕ} {x : ℤ} (hx : fblock s x) : fmin s ≤ x := by
  obtain ⟨hs,i,hi,his,rfl⟩ := hx
  by_cases hi2 : i=2
  · subst i
    exact le_rfl
  by_cases hip : i%2=0
  · have h := fentry_order s 2 i hs his (by simpa using hip.symm) (by omega)
    norm_num at h
    exact h.le
  · have h1 := fbelow s 2 hs (by decide)
    have h2 := fabove s i his hip
    unfold fmin
    omega

private theorem fmax_bound {s : ℕ} {x : ℤ} (hx : fblock s x) : x ≤ fmax s := by
  obtain ⟨hs,i,hi,his,rfl⟩ := hx
  by_cases h : 6 ≤ s
  · rw [fmax,if_pos h]
    by_cases hi3 : i=3
    · subst i
      exact le_rfl
    by_cases hip : i%2=0
    · have h1 := fbelow s i his hip
      have h2 := fabove s 3 h (by decide)
      omega
    · have h := fentry_order s 3 i h his (by simp; omega) (by omega)
      norm_num at h
      exact h.le
  · have hi2 : i=2 := by omega
    subst i
    rw [fmax,if_neg h]


private theorem fstep_gap (s i : ℕ) (his : 2*(i+2) ≤ s) :
    if i%2=0 then fentry s (i+2) - fentry s i = F (s-2*i-2)
    else fentry s i - fentry s (i+2) = F (s-2*i-2) := by
  have hi : 2*i ≤ s := by omega
  have hf := ldiff (s-2*(i+2))
  rw [show s-2*(i+2)+4=s-2*i by omega,
    show s-2*(i+2)+2=s-2*i-2 by omega] at hf
  change L (s-2*i) - L (s-2*(i+2)) = 5 * F (s-2*i-2) at hf
  have h1 := fentry_formula s i hi
  have h2 := fentry_formula s (i+2) his
  rw [show (i+2)%2=i%2 by omega] at h2
  split
  next hp =>
    simp only [if_pos hp] at h1 h2
    omega
  next hp =>
    simp only [if_neg hp] at h1 h2
    omega

private theorem fsmall_gap (i : ℕ) (hi : 1 ≤ i) : FProduct (F i) :=
  ⟨1,i,by decide,hi,by norm_num⟩

private theorem fphase_close (s i j : ℕ) (his : 2*i ≤ s) (hjs : 2*j ≤ s)
    (hpar : i%2=j%2) (hij : i<j)
    (hc : ∀ z : ℤ, FProduct z →
      ¬((fentry s i < z ∧ z < fentry s j) ∨ (fentry s j < z ∧ z < fentry s i))) :
    j=i+2 := by
  have h2 : i+2 ≤ j := by omega
  by_contra hne
  have hz : FProduct (fentry s (i+2)) :=
    fmember_of_block ⟨by omega,i+2,by omega,by omega,rfl⟩
  have hl := fentry_order s i (i+2) his (by omega) (by omega) (by omega)
  have hu := fentry_order s (i+2) j (by omega) hjs (by omega) (by omega)
  rw [show (i+2)%2=i%2 by omega] at hu
  by_cases h : i%2=0
  · simp only [if_pos h] at hl hu
    exact hc _ hz (Or.inl ⟨hl,hu⟩)
  · simp only [if_neg h] at hl hu
    exact hc _ hz (Or.inr ⟨hu,hl⟩)

private theorem fblock_gap {s : ℕ} {x y : ℤ} (hx : fblock s x) (hy : fblock s y)
    (hlt : x<y) (hc : ∀ z : ℤ, x<z → z<y → ¬FProduct z) : FProduct (y-x) := by
  obtain ⟨hs,i,hi,his,rfl⟩ := hx
  obtain ⟨_,j,hj,hjs,rfl⟩ := hy
  have hnc : i ≠ j := by intro h; subst j; omega
  have hl (z : ℤ) (hz : FProduct z) :
      ¬((fentry s i < z ∧ z < fentry s j) ∨ (fentry s j < z ∧ z < fentry s i)) := by
    rintro (⟨hl,hu⟩ | ⟨hl,hu⟩)
    · exact hc _ hl hu hz
    · omega
  by_cases hip : i%2=0
  · by_cases hjp : j%2=0
    · have hin : i<j := by
        by_contra! h
        have he := fentry_order s j i hjs his (hjp.trans hip.symm) (by omega)
        simp only [if_pos hjp] at he
        omega
      have hj' : j=i+2 := fphase_close s i j his hjs (hip.trans hjp.symm) hin hl
      subst j
      have he := fstep_gap s i hjs
      simp only [if_pos hip] at he
      rw [he]
      exact fsmall_gap _ (by omega)
    · have hid : s-2*i ≤ 3 := by
        by_contra! hbad
        have hi2 : 2*(i+2) ≤ s := by omega
        have hOrd := fentry_order s i (i+2) his hi2 (by omega) (by omega)
        simp only [if_pos hip] at hOrd
        have hBelow := fbelow s (i+2) hi2 (by omega)
        have hAbove := fabove s j hjs hjp
        have hmid : FProduct (fentry s (i+2)) :=
          fmember_of_block ⟨hs,i+2,by omega,hi2,rfl⟩
        exact hc _ hOrd (by omega) hmid
      have hjd : s-2*j ≤ 3 := by
        by_contra! hbad
        have hj2 : 2*(j+2) ≤ s := by omega
        have hOrd := fentry_order s j (j+2) hjs hj2 (by omega) (by omega)
        simp only [if_neg hjp] at hOrd
        have hBelow := fbelow s i his hip
        have hAbove := fabove s (j+2) hj2 (by omega)
        have hmid : FProduct (fentry s (j+2)) :=
          fmember_of_block ⟨hs,j+2,by omega,hj2,rfl⟩
        exact hc _ (by omega) hOrd hmid
      have hpair : (s-2*i=0 ∧ s-2*j=2) ∨ (s-2*i=1 ∧ s-2*j=3) ∨
          (s-2*i=2 ∧ s-2*j=0) ∨ (s-2*i=3 ∧ s-2*j=1) := by omega
      have hSum : L (s-2*i)+L (s-2*j)=5 := by
        rcases hpair with h|h|h|h <;> rw [h.1,h.2] <;> decide
      have hI := fentry_formula s i his
      have hJ := fentry_formula s j hjs
      simp only [if_pos hip] at hI
      simp only [if_neg hjp] at hJ
      have hg : fentry s j-fentry s i=1 := by omega
      rw [hg]
      exact ⟨1,1,by decide,by decide,by decide⟩
  · by_cases hjp : j%2=0
    · have h1 := fabove s i his hip
      have h2 := fbelow s j hjs hjp
      omega
    · have hin : j<i := by
        by_contra! h
        have he := fentry_order s i j his hjs (by omega) (by omega)
        simp only [if_neg hip] at he
        omega
      have hi' : i=j+2 := fphase_close s j i hjs his (by omega) hin
        (by intro z hz; simpa [or_comm] using hl z hz)
      subst i
      have he := fstep_gap s j his
      simp only [if_neg hjp] at he
      rw [he]
      exact fsmall_gap _ (by omega)


private theorem left_boundary (s : ℕ) (hs : 6 ≤ s) :
    minValue s - fmax (s+3) = 2 * F (s-6) := by
  obtain ⟨d,rfl⟩ : ∃ d, s=d+6 := ⟨s-6,by omega⟩
  rw [minValue,if_pos (by omega),fmax,if_pos (by omega)]
  change 4*L (d+3)-2*F (d+6)=2*F (d+6-6)
  rw [show d+6-6=d by omega,show d+3=d+2+1 by omega,l_fib]
  have h1 := fs d
  have h2 := fs (d+1)
  have h3 := fs (d+2)
  have h4 := fs (d+3)
  have h5 := fs (d+4)
  simp only [Nat.add_assoc,Nat.reduceAdd] at h2 h3 h4 h5 ⊢
  linarith only [h1,h2,h3,h4,h5]

private theorem right_boundary (s : ℕ) (hs : 6 ≤ s) :
    fmin (s+4) - maxValue s = F (s-6) := by
  obtain ⟨d,rfl⟩ : ∃ d, s=d+6 := ⟨s-6,by omega⟩
  have hfm : fmin ((d+6)+4)=F (d+8) := by
    unfold fmin fentry
    rw [show F 2=1 from rfl,one_mul,show d+6+4-2=d+8 by omega]
  rw [hfm,maxValue,if_pos (by omega)]
  change F (d+8)-3*L (d+4)=F (d+6-6)
  rw [show d+6-6=d by omega,show d+4=d+3+1 by omega,l_fib]
  have h1 := fs d
  have h2 := fs (d+1)
  have h3 := fs (d+2)
  have h4 := fs (d+3)
  have h5 := fs (d+4)
  have h6 := fs (d+5)
  have h7 := fs (d+6)
  simp only [Nat.add_assoc,Nat.reduceAdd] at h2 h3 h4 h5 h6 h7 ⊢
  linarith only [h1,h2,h3,h4,h5,h6,h7]

private def mixed (s : ℕ) (x : ℤ) : Prop :=
  14 ≤ s ∧ (if s%2=0 then block (s/2) x else fblock (s/2+4) x)

private def umin (s : ℕ) := if s%2=0 then minValue (s/2) else fmin (s/2+4)
private def umax (s : ℕ) := if s%2=0 then maxValue (s/2) else fmax (s/2+4)

private theorem umin_mem {s : ℕ} (hs : 14 ≤ s) : mixed s (umin s) := by
  refine ⟨hs,?_⟩
  unfold umin
  by_cases h : s%2=0
  · simp only [if_pos h]
    exact min_mem (by omega)
  · simp only [if_neg h]
    exact fmin_mem (by omega)

private theorem umax_mem {s : ℕ} (hs : 14 ≤ s) : mixed s (umax s) := by
  refine ⟨hs,?_⟩
  unfold umax
  by_cases h : s%2=0
  · simp only [if_pos h]
    exact max_mem (by omega)
  · simp only [if_neg h]
    exact fmax_mem (by omega)

private theorem member_of_mixed {s : ℕ} {x : ℤ} (hx : mixed s x) : Both x := by
  obtain ⟨_,h⟩ := hx
  split at h
  · exact Or.inl (member_of_block h)
  · exact Or.inr (fmember_of_block h)

private theorem umin_bound {s : ℕ} {x : ℤ} (hx : mixed s x) : umin s ≤ x := by
  obtain ⟨_,h⟩ := hx
  unfold umin
  split at h
  next hp => simp only [if_pos hp]; exact min_bound h
  next hp => simp only [if_neg hp]; exact fmin_bound h

private theorem umax_bound {s : ℕ} {x : ℤ} (hx : mixed s x) : x ≤ umax s := by
  obtain ⟨_,h⟩ := hx
  unfold umax
  split at h
  next hp => simp only [if_pos hp]; exact max_bound h
  next hp => simp only [if_neg hp]; exact fmax_bound h

private theorem uboundary (s : ℕ) (hs : 14 ≤ s) :
    umin (s+1) - umax s =
      if s%2=0 then F (s/2-6) else 2*F ((s+1)/2-6) := by
  unfold umin umax
  by_cases h : s%2=0
  · have h1 : (s+1)%2 ≠ 0 := by omega
    have h2 : (s+1)/2=s/2 := by omega
    simp only [if_pos h,if_neg h1,h2]
    exact right_boundary (s/2) (by omega)
  · have h1 : (s+1)%2=0 := by omega
    have h2 : s/2+4=(s+1)/2+3 := by omega
    simp only [if_pos h1,if_neg h,h2]
    exact left_boundary ((s+1)/2) (by omega)

private theorem useparate {s : ℕ} (hs : 14 ≤ s) : umax s < umin (s+1) := by
  have h := uboundary s hs
  split at h
  · have hF := fp (s/2-6) (by omega)
    omega
  · have hF := fp ((s+1)/2-6) (by omega)
    omega

private theorem umin_mono {s t : ℕ} (hs : 14 ≤ s) (hst : s ≤ t) : umin s ≤ umin t := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t ht ih =>
    have h0 : umin t ≤ umax t := umax_bound (umin_mem (by omega))
    have h1 : umax t < umin (t+1) := useparate (by omega)
    exact ih.trans (h0.trans h1.le)

private theorem mixed_order {s t : ℕ} {x y : ℤ}
    (hx : mixed s x) (hy : mixed t y) (hst : s<t) : x<y := by
  have h1 := umax_bound hx
  have h2 := useparate hx.1
  have h3 : umin (s+1) ≤ umin t := umin_mono (by have := hx.1; omega) (by omega)
  have h4 := umin_bound hy
  omega

private theorem mixed_gap {s t : ℕ} {x y : ℤ} (hx : mixed s x) (hy : mixed t y)
    (hc : ConsecutiveBoth x y) : Both (y-x) := by
  by_cases he : s=t
  · subst t
    have hS := hx.2
    have hT := hy.2
    split at hS
    next h =>
      simp only [if_pos h] at hT
      have hl : Consecutive x y := ⟨hc.1,member_of_block hS,member_of_block hT,
        fun z h0 h1 hz => hc.2.2.2 z h0 h1 (Or.inl hz)⟩
      exact same_block_gap hS hT hl
    next h =>
      simp only [if_neg h] at hT
      exact Or.inr (fblock_gap hS hT hc.1 (fun z h0 h1 hz =>
        hc.2.2.2 z h0 h1 (Or.inr hz)))
  have hs := hx.1
  have ht := hy.1
  have hst : s<t := by
    by_contra! h
    have hl := mixed_order hy hx (by omega)
    have hu := hc.1
    omega
  have hsucc : t=s+1 := by
    by_contra h
    have hm := umin_mem (s:=s+1) (by omega)
    exact hc.2.2.2 _ (mixed_order hx hm (by omega)) (mixed_order hm hy (by omega))
      (member_of_mixed hm)
  have hmax : x=umax s := by
    have hh := umax_bound hx
    by_contra h
    have hm := umax_mem hs
    exact hc.2.2.2 _ (by omega) (mixed_order hm hy hst) (member_of_mixed hm)
  have hmin : y=umin t := by
    have hh := umin_bound hy
    by_contra h
    have hm := umin_mem ht
    exact hc.2.2.2 _ (mixed_order hx hm hst) (by omega) (member_of_mixed hm)
  rw [hmax,hmin,hsucc,uboundary s hs]
  split
  · exact Or.inr (fsmall_gap _ (by omega))
  · exact Or.inr ⟨3,(s+1)/2-6,by decide,by omega,rfl⟩


private def Small (x : ℤ) : Prop :=
    x ∈ ({1,2,3,4,5,6,7,8,9,10,11,12,13,15,16,18,21,24,25,26} : Finset ℤ)

private instance (x : ℤ) : Decidable (Small x) := by unfold Small; infer_instance

private theorem small_bounds {x : ℤ} (h : Small x) : 1 ≤ x ∧ x ≤ 26 := by
  simp only [Small,Finset.mem_insert,Finset.mem_singleton] at h
  omega

private theorem either_block {x : ℤ} (h : Both x) : Small x ∨ ∃ s, mixed s x := by
  rcases h with hL|hF
  · obtain ⟨s,hs⟩ := mem_block hL
    by_cases hs' : 7 ≤ s
    · refine Or.inr ⟨2*s,by omega,?_⟩
      simp only [show 2*s%2=0 by omega,if_pos,show 2*s/2=s by omega]
      exact hs
    · left
      obtain ⟨hs0,rfl | ⟨i,hi,his,rfl⟩⟩ := hs
      · interval_cases s <;> decide
      · have htop : i ≤ 3 := by omega
        interval_cases s <;> interval_cases i <;> first | omega | decide
  · obtain ⟨s,hs⟩ := fmem_block hF
    by_cases hs' : 11 ≤ s
    · refine Or.inr ⟨2*(s-4)+1,by omega,?_⟩
      simp only [if_neg (show (2*(s-4)+1)%2≠0 by omega),
        show (2*(s-4)+1)/2+4=s by omega]
      exact hs
    · left
      obtain ⟨hs0,i,hi,his,rfl⟩ := hs
      have htop : i ≤ 5 := by omega
      interval_cases s <;> interval_cases i <;> first | omega | decide

private theorem small_member {x : ℤ} (hx : Small x) : Both x := by
  simp only [Small,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Or.inl ⟨1,1,by decide,by decide,by decide⟩
  · exact Or.inr ⟨1,3,by decide,by decide,by decide⟩
  · exact Or.inl ⟨1,2,by decide,by decide,by decide⟩
  · exact Or.inl ⟨1,3,by decide,by decide,by decide⟩
  · exact Or.inr ⟨1,5,by decide,by decide,by decide⟩
  · exact Or.inr ⟨3,4,by decide,by decide,by decide⟩
  · exact Or.inl ⟨1,4,by decide,by decide,by decide⟩
  · exact Or.inr ⟨1,6,by decide,by decide,by decide⟩
  · exact Or.inl ⟨2,2,by decide,by decide,by decide⟩
  · exact Or.inr ⟨3,5,by decide,by decide,by decide⟩
  · exact Or.inl ⟨1,5,by decide,by decide,by decide⟩
  · exact Or.inl ⟨2,3,by decide,by decide,by decide⟩
  · exact Or.inr ⟨1,7,by decide,by decide,by decide⟩
  · exact Or.inr ⟨4,5,by decide,by decide,by decide⟩
  · exact Or.inl ⟨3,3,by decide,by decide,by decide⟩
  · exact Or.inl ⟨1,6,by decide,by decide,by decide⟩
  · exact Or.inl ⟨2,4,by decide,by decide,by decide⟩
  · exact Or.inr ⟨4,6,by decide,by decide,by decide⟩
  · exact Or.inr ⟨5,5,by decide,by decide,by decide⟩
  · exact Or.inr ⟨3,7,by decide,by decide,by decide⟩

private theorem small_certificate :
    ∀ x y : Fin 27, Small (x.val : ℤ) → Small (y.val : ℤ) → x < y →
      (∀ z : Fin 27, x < z → z < y → ¬ Small (z.val : ℤ)) →
      (1 ≤ (y.val : ℤ)-(x.val : ℤ) ∧ (y.val : ℤ)-(x.val : ℤ) ≤ 3) := by
  decide +kernel

private theorem small_gap_both {x y : ℤ} (hx : Small x) (hy : Small y)
    (hc : ConsecutiveBoth x y) : Both (y-x) := by
  have hxRange := small_bounds hx
  have hyRange := small_bounds hy
  let a : Fin 27 := ⟨x.toNat,by omega⟩
  let b : Fin 27 := ⟨y.toNat,by omega⟩
  have ha : (a.val : ℤ)=x := Int.toNat_of_nonneg (by omega)
  have hb : (b.val : ℤ)=y := Int.toNat_of_nonneg (by omega)
  have hab : a<b := by
    have hxy := hc.1
    rw [←ha,←hb] at hxy
    exact_mod_cast hxy
  have hmid (z : Fin 27) (haz : a<z) (hzb : z<b) : ¬Small (z.val : ℤ) := by
    intro hz
    have hz1 : (a.val : ℤ) < (z.val : ℤ) := by exact_mod_cast haz
    have hz2 : (z.val : ℤ) < (b.val : ℤ) := by exact_mod_cast hzb
    rw [ha] at hz1
    rw [hb] at hz2
    exact hc.2.2.2 _ hz1 hz2 (small_member hz)
  have hg := small_certificate a b (ha.symm ▸ hx) (hb.symm ▸ hy) hab hmid
  rw [ha,hb] at hg
  have hi : y-x=1 ∨ y-x=2 ∨ y-x=3 := by omega
  rcases hi with h|h|h <;> rw [h]
  · exact Or.inr ⟨1,1,by decide,by decide,by decide⟩
  · exact Or.inr ⟨1,3,by decide,by decide,by decide⟩
  · exact Or.inr ⟨1,4,by decide,by decide,by decide⟩

private theorem large_bound {s : ℕ} {x : ℤ} (h : mixed s x) : 28 ≤ x := by
  have hmin : umin 14 ≤ umin s := umin_mono (by decide) h.1
  have hu : umin 14=28 := by decide
  rw [hu] at hmin
  exact hmin.trans (umin_bound h)

private theorem transition_gap {x y : ℤ} {s : ℕ} (hx : Small x) (hy : mixed s y)
    (hc : ConsecutiveBoth x y) : Both (y-x) := by
  have hsmall := small_bounds hx
  have hy28 := large_bound hy
  have x26 : x=26 := by
    by_contra h
    exact hc.2.2.2 26 (by omega) (by omega) (small_member (by decide))
  have y28 : y=28 := by
    by_contra h
    have h28 : mixed 14 28 := by
      change 14≤14 ∧ (if 14%2=0 then block 7 28 else fblock 11 28)
      refine ⟨by decide,?_⟩
      norm_num
      exact ⟨by decide,Or.inr ⟨3,by decide,by decide,by decide⟩⟩
    exact hc.2.2.2 28 (by omega) (by omega) (member_of_mixed h28)
  rw [x26,y28]
  exact Or.inr ⟨1,3,by decide,by decide,by decide⟩

theorem main : ∀ x y : ℤ, ConsecutiveBoth x y → Both (y-x) := by
  intro x y hc
  obtain hx|⟨s,hx⟩ := either_block hc.2.1
  · obtain hy|⟨t,hy⟩ := either_block hc.2.2.1
    · exact small_gap_both hx hy hc
    · exact transition_gap hx hy hc
  · obtain hy|⟨t,hy⟩ := either_block hc.2.2.1
    · have h1 := large_bound hx
      have h2 := small_bounds hy
      have := hc.1
      omega
    · exact mixed_gap hx hy hc

end OpenMath.A272917

theorem OMA.solution : type_of% @OMA.S_oeis_a272917.main :=
  OpenMath.A272917.main
