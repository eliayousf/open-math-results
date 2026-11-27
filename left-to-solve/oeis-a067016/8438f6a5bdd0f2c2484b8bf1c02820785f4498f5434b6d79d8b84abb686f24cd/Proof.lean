import OMAStatements.S_oeis_a067016
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OpenMath.A067016

open Finset

open OMA.S_oeis_a067016 (a)

private theorem a_zero : a 0 = 1 := by simp [a]
private theorem a_one : a 1 = 4 := by simp [a]
private theorem a_two : a 2 = 3 := by simp [a]
private theorem a_three : a 3 = 2 := by simp [a]

private theorem a_four : a 4 = 7 := by
  rw [a]
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    fin_cases i <;> norm_num [a_zero, a_one, a_two, a_three]
  · exact le_sup_of_le (b := (1 : Fin 4)) (mem_univ _) (by
      norm_num [a_one, a_two])

private theorem a_five : a 5 = 8 := by
  rw [a]
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    fin_cases i <;> norm_num [a_zero, a_one, a_two, a_three, a_four]
  · exact le_sup_of_le (b := (0 : Fin 5)) (mem_univ _) (by
      norm_num [a_zero, a_four])

def closed (n : ℕ) : ℕ := 2*n - (if n % 2 = 0 then 1 else 2)

private theorem closed_bound (n : ℕ) :
    2*n - 2 ≤ closed n ∧ closed n ≤ 2*n - 1 := by
  unfold closed
  split <;> omega

private theorem closed_shift (n : ℕ) (hn : 4 ≤ n) :
    closed (n+2) = closed n + 4 := by
  unfold closed
  rw [show (n+2)%2 = n%2 by omega]
  split <;> omega

theorem formula (n : ℕ) (hn : 4 ≤ n) : a n = closed n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hl : n ≤ 5
    · interval_cases n <;> norm_num [a_four, a_five, closed]
    have hbound (m : ℕ) (hm : m < n) (hm2 : 2 ≤ m) : a m ≤ 2*m - 1 := by
      by_cases hh : 4 ≤ m
      · rw [ih m hm hh]
        exact (closed_bound m).2
      · interval_cases m <;> norm_num [a_two, a_three]
    obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
    have he : a (k+2) = closed (k+2) := ih (k+2) (by omega) (by omega)
    have htail : closed (k+4) = closed (k+2)+4 := closed_shift (k+2) (by omega)
    rw [a]
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      generalize hi : (i : ℕ) = x
      have hx : x < k+4 := hi ▸ i.isLt
      set y := k+3-x
      change a x + a y ≤ closed (k+4)
      have hsum : x+y=k+3 := by omega
      have hy : y < k+4 := by omega
      by_cases hx1 : x = 1
      · have hy2 : y=k+2 := by omega
        rw [hx1, hy2, a_one, he, htail]
        omega
      by_cases hy1 : y = 1
      · have hx2 : x=k+2 := by omega
        rw [hx2, hy1, a_one, he, htail]
      have ht := (closed_bound (k+4)).1
      by_cases hx0 : x = 0
      · rw [hx0, a_zero]
        have hy' := hbound y hy (by omega)
        omega
      by_cases hy0 : y = 0
      · rw [hy0, a_zero]
        have hx' := hbound x hx (by omega)
        omega
      have hx' := hbound x hx (by omega)
      have hy' := hbound y hy (by omega)
      omega
    · have hw : a 1 + a (k+3-1) ≤
          univ.sup (fun i : Fin (k + 4) => a i + a (k + 3 - i)) :=
        le_sup (f := fun i : Fin (k + 4) => a i + a (k + 3 - i))
          (b := ⟨1, by omega⟩) (mem_univ _)
      rw [a_one, show k+3-1=k+2 by omega, he] at hw
      omega

open PowerSeries in
theorem generating_function :
    (1-X)^2 * (1+X) * mk (fun n => (a n : ℤ)) =
      1 + 3*X - 2*X^2 - 4*X^3 + 6*X^4 + 2*X^5 - 2*X^6 := by
  have hd : ((1-X)^2 * (1+X) : ℤ⟦X⟧) = 1 - X^1 - X^2 + X^3 := by
    simp
    ring
  have hp : (1 + 3*X - 2*X^2 - 4*X^3 + 6*X^4 + 2*X^5 - 2*X^6 : ℤ⟦X⟧) =
      C 1 + C 3*X^1 - C 2*X^2 - C 4*X^3 + C 6*X^4 + C 2*X^5 - C 2*X^6 := by simp
  rw [hd, hp]
  ext n
  simp only [sub_mul, add_mul, one_mul, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_C]
  by_cases hn : n < 7
  · have h6 : a 6 = 11 := by norm_num [formula 6 (by decide), closed]
    interval_cases n <;> norm_num [a_zero, a_one, a_two, a_three, a_four, a_five, h6]
  · simp [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega]
    have h1 : a n = a (n-2) + 4 := by
      rw [formula n (by omega), formula (n-2) (by omega), ← show n-2+2=n by omega]
      exact closed_shift _ (by omega)
    have h2 : a (n-1) = a (n-3) + 4 := by
      rw [formula (n-1) (by omega), formula (n-3) (by omega),
        ← show n-3+2=n-1 by omega]
      exact closed_shift _ (by omega)
    omega

private theorem neg_one_pow (n : ℕ) :
    (-1 : ℤ)^n = if n%2=0 then 1 else -1 := by
  calc
    _ = (-1 : ℤ)^(2*(n/2)+n%2) := by
      congr 1
      omega
    _ = (-1 : ℤ)^(n%2) := by rw [pow_add, pow_mul]; norm_num
    _ = _ := by
      have h : n%2=0 ∨ n%2=1 := by omega
      rcases h with h | h <;> simp [h]

private theorem displayed_formula (n : ℕ) (hn : 4 ≤ n) :
    2 * (a n : ℤ) = -3 + (-1 : ℤ)^n + 4*(n : ℤ) := by
  rw [neg_one_pow, formula n hn]
  unfold closed
  by_cases h : n%2=0
  · simp only [if_pos h]
    rw [Nat.cast_sub (by omega : 1 ≤ 2*n)]
    push_cast
    ring
  · simp only [if_neg h]
    rw [Nat.cast_sub (by omega : 2 ≤ 2*n)]
    push_cast
    ring

open PowerSeries in
theorem main :
    (∀ n ≥ 4, 2 * (a n : ℤ) = -3 + (-1 : ℤ)^n + 4*(n : ℤ)) ∧
    ((1-X)^2 * (1+X) * mk (fun n => (a n : ℤ)) =
      1 + 3*X - 2*X^2 - 4*X^3 + 6*X^4 + 2*X^5 - 2*X^6) :=
  ⟨displayed_formula, generating_function⟩

end OpenMath.A067016

theorem OMA.solution : type_of% @OMA.S_oeis_a067016.main := OpenMath.A067016.main
