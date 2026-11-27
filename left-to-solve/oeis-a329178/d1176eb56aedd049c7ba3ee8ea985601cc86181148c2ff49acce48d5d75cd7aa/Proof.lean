import OMAStatements.S_oeis_a329178
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace A329178Proof

open OMA.S_oeis_a329178 PowerSeries Finset

private def adjacent (n : ℕ) : ℤ := padovan (n+7) * padovan (n+8)

private theorem a_eq (n : ℕ) : a n = adjacent n - 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    unfold a
    rw [sum_range_succ]
    change a n + padovan (n+6)*padovan (n+8) = _
    rw [ih]
    have hp : padovan (n+9) = padovan (n+7) + padovan (n+6) := rfl
    unfold adjacent
    change padovan (n+7)*padovan (n+8)-1 + padovan (n+6)*padovan (n+8) =
      padovan (n+8)*padovan (n+9)-1
    rw [hp]
    ring

private theorem adjacent_recurrence (n : ℕ) :
    adjacent (n+6) = adjacent (n+5) + adjacent (n+4) + adjacent (n+3)
      - adjacent (n+2) + adjacent (n+1) - adjacent n := by
  simp only [adjacent, Nat.add_assoc, Nat.reduceAdd, padovan]
  ring

private theorem recurrence (n : ℕ) (hn : 6 < n) :
    a n = 2*a (n-1)-2*a (n-4)+2*a (n-5)-2*a (n-6)+a (n-7) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n=k+7 := ⟨n-7, by omega⟩
  rw [show k+7-1=k+6 by omega, show k+7-4=k+3 by omega, show k+7-5=k+2 by omega,
    show k+7-6=k+1 by omega, show k+7-7=k by omega]
  simp only [a_eq]
  have h0 := adjacent_recurrence k
  have h1 := adjacent_recurrence (k+1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1
  omega

private theorem gf : ((1-X)*(1-2*X+X^2-X^3)*(1+X-X^3) : ℤ⟦X⟧)*mk a =
    1+X-X^2+X^3-X^4 := by
  have hd : ((1-X)*(1-2*X+X^2-X^3)*(1+X-X^3) : ℤ⟦X⟧) =
      1-C 2*X^1+C 2*X^4-C 2*X^5+C 2*X^6-X^7 := by norm_num; ring
  rw [hd]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_one, coeff_X, coeff_X_pow]
  by_cases hn : n < 7
  · interval_cases n <;> decide
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega), if_pos (show 7 ≤ n by omega),
      if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega)]
    have h := recurrence n (by omega)
    omega

end A329178Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a329178.main :=
  ⟨A329178Proof.gf, A329178Proof.recurrence⟩
