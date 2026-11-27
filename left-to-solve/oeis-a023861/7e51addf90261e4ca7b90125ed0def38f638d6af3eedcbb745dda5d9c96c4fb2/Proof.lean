import OMAStatements.S_oeis_a023861
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

namespace OpenMath.A023861

open Finset PowerSeries

open OMA.S_oeis_a023861

private theorem partial_succ (n m : ℕ) :
    weightedSum n (m + 1) = weightedSum n m + (m + 1 : ℕ) * lucas (n - m) := by
  simp only [weightedSum, Finset.sum_range_succ]

private theorem partial_recur (n m : ℕ) (hm : m ≤ n + 1) :
    weightedSum (n + 2) m = weightedSum (n + 1) m + weightedSum n m := by
  unfold weightedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n + 2 - k = (n - k) + 2 by omega, lucas,
    show n + 1 - k = (n - k) + 1 by omega, mul_add]

private def d (n : ℕ) : ℤ := a (n + 2) - a (n + 1) - a n

private theorem d_even (n : ℕ) : d (2 * n) = (n + 1 : ℕ) * lucas n := by
  unfold d a
  rw [show (2*n+2+1)/2 = n+1 by omega,
    show (2*n+1+1)/2 = n+1 by omega, show (2*n+1)/2 = n by omega,
    partial_succ (2*n+2), partial_succ (2*n+1), partial_recur (2*n) n (by omega),
    show 2*n+2-n = n+2 by omega, show 2*n+1-n = n+1 by omega, lucas]
  ring

private theorem d_odd (n : ℕ) : d (2 * n + 1) = (n + 2 : ℕ) * lucas (n + 2) := by
  unfold d a
  rw [show (2*n+1+2+1)/2 = (n+1)+1 by omega,
    show (2*n+1+1+1)/2 = n+1 by omega, show (2*n+1+1)/2 = n+1 by omega,
    partial_succ, partial_recur (2*n+1) (n+1) (by omega),
    show 2*n+1+2-(n+1)=n+2 by omega]
  ring

private theorem weighted_recur (k offset c : ℕ) :
    (k + 4 + c : ℕ) * lucas (offset + k + 4) =
    2 * (k + 3 + c : ℕ) * lucas (offset + k + 3) +
      (k + 2 + c : ℕ) * lucas (offset + k + 2) -
      2 * (k + 1 + c : ℕ) * lucas (offset + k + 1) -
      (k + c : ℕ) * lucas (offset + k) := by
  have h2 : lucas (offset + k + 2) = lucas (offset + k + 1) + lucas (offset + k) := rfl
  have h3 : lucas (offset + k + 3) = lucas (offset + k + 2) + lucas (offset + k + 1) := rfl
  have h4 : lucas (offset + k + 4) = lucas (offset + k + 3) + lucas (offset + k + 2) := rfl
  simp only [h4, h3, h2, Nat.cast_add, Nat.cast_ofNat]
  ring

private theorem d_recur (n : ℕ) :
    d (n + 8) = 2*d (n + 6) + d (n + 4) - 2*d (n + 2) - d n := by
  let k := n / 2
  obtain he | ho : n = 2*k ∨ n = 2*k+1 := by omega
  · rw [show n+8=2*(k+4) by omega, show n+6=2*(k+3) by omega,
      show n+4=2*(k+2) by omega, show n+2=2*(k+1) by omega, he]
    simpa only [d_even, zero_add, Nat.cast_add, Nat.cast_ofNat, mul_assoc] using weighted_recur k 0 1
  · rw [show n+8=2*(k+4)+1 by omega, show n+6=2*(k+3)+1 by omega,
      show n+4=2*(k+2)+1 by omega, show n+2=2*(k+1)+1 by omega, ho]
    simp only [d_odd]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_assoc] using
      weighted_recur k 2 2

private theorem first_coeff (n : ℕ) :
    coeff n (((1-X-X^2 : ℤ⟦X⟧) * mk a)) =
      a n - (if 1 ≤ n then a (n-1) else 0) - (if 2 ≤ n then a (n-2) else 0) := by
  have hp : (1-X-X^2 : ℤ⟦X⟧) = 1-X^1-X^2 := by simp
  rw [hp]
  simp only [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_mk]

private theorem first_shifted (n : ℕ) :
    coeff (n+2) (((1-X-X^2 : ℤ⟦X⟧) * mk a)) = d n := by
  rw [first_coeff, if_pos (by omega), if_pos (by omega),
    show n+2-1 = n+1 by omega, show n+2-2 = n by omega, d]

private theorem second_coeff (n : ℕ) (P : ℤ⟦X⟧) :
    coeff n (((1-X^2-X^4 : ℤ⟦X⟧)^2) * P) =
      coeff n P - 2*(if 2 ≤ n then coeff (n-2) P else 0) -
        (if 4 ≤ n then coeff (n-4) P else 0) +
        2*(if 6 ≤ n then coeff (n-6) P else 0) + (if 8 ≤ n then coeff (n-8) P else 0) := by
  have hp : ((1-X^2-X^4 : ℤ⟦X⟧)^2) =
      1 - C 2 * X^2 - X^4 + C 2 * X^6 + X^8 := by
    simp
    ring
  rw [hp]
  simp only [sub_mul, add_mul, one_mul, map_add, map_sub, mul_assoc, coeff_C_mul, coeff_X_pow_mul']

/-- The conjectured ordinary generating function after clearing its denominator. -/
theorem main : ((1-X-X^2 : ℤ⟦X⟧) * (1-X^2-X^4)^2) * mk a =
    X + C 2 * X^2 + C 4 * X^3 - C 2 * X^4 - X^5 + C 3 * X^6 := by
  rw [mul_comm (1-X-X^2 : ℤ⟦X⟧), mul_assoc]
  ext n
  rw [second_coeff]
  by_cases hn : n < 10
  · interval_cases n <;>
      simp only [map_add, map_sub, coeff_X, coeff_X_pow, coeff_C_mul] <;>
      norm_num [first_coeff, a, weightedSum, lucas, Finset.sum_range_succ]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 10 := ⟨n - 10, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      show k+10 = (k+8)+2 by omega, first_shifted,
      show k+8+2-2 = (k+6)+2 by omega, first_shifted,
      show k+8+2-4 = (k+4)+2 by omega, first_shifted,
      show k+8+2-6 = (k+2)+2 by omega, first_shifted,
      show k+8+2-8 = k+2 by omega, first_shifted]
    rw [d_recur]
    simp only [map_add, map_sub, coeff_X, coeff_C_mul, coeff_X_pow]
    split_ifs <;> omega

end OpenMath.A023861


theorem OMA.solution : type_of% @OMA.S_oeis_a023861.main := OpenMath.A023861.main
