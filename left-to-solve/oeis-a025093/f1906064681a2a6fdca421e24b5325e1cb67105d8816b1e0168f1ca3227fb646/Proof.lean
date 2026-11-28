import OMAStatements.S_oeis_a025093
import Mathlib

/-!
Colin Barker conjectured the recurrence and generating function for A025093.
Source: https://oeis.org/A025093
-/

namespace A025093Proof

open OMA.S_oeis_a025093 PowerSeries

private def truncated_sum (n k : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc 1 k, L i * (2 * ((n : ℤ) - i) + 3)

private theorem partial_succ (n k : ℕ) :
    truncated_sum n (k + 1) = truncated_sum n k + L (k + 1) * (2 * ((n : ℤ) - (k + 1 : ℕ)) + 3) := by
  unfold truncated_sum
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]

private theorem partial_linear (n k : ℕ) :
    truncated_sum (n + 2) k - 2 * truncated_sum (n + 1) k + truncated_sum n k = 0 := by
  unfold truncated_sum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  push_cast
  ring

private def second (n : ℕ) : ℤ := a (n + 2) - 2 * a (n + 1) + a n

private theorem second_even (k : ℕ) : second (2 * k) = -(2 * (k : ℤ) + 1) * L (k + 1) := by
  unfold second a
  have h₀ : (2 * k + 1) / 2 = k := by omega
  have h₁ : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h₂ : (2 * k + 2 + 1) / 2 = k + 1 := by omega
  rw [h₂, h₁, h₀]
  change truncated_sum (2 * k + 2) (k + 1) - 2 * truncated_sum (2 * k + 1) (k + 1) +
    truncated_sum (2 * k) k = _
  rw [partial_succ (2 * k + 2) k, partial_succ (2 * k + 1) k]
  push_cast
  linear_combination partial_linear (2 * k) k

private theorem second_odd (k : ℕ) : second (2 * k + 1) = (2 * (k : ℤ) + 5) * L (k + 2) := by
  unfold second a
  have h₀ : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h₁ : (2 * k + 1 + 1 + 1) / 2 = k + 1 := by omega
  have h₂ : (2 * k + 1 + 2 + 1) / 2 = k + 2 := by omega
  rw [h₂, h₁, h₀]
  change truncated_sum ((2 * k + 1) + 2) ((k + 1) + 1) -
    2 * truncated_sum ((2 * k + 1) + 1) (k + 1) + truncated_sum (2 * k + 1) (k + 1) = _
  rw [partial_succ ((2 * k + 1) + 2) (k + 1)]
  push_cast
  linear_combination partial_linear (2 * k + 1) (k + 1)

private def weighted (b c : ℤ) (m : ℕ) : ℤ := (b * (m : ℤ) + c) * L m

private theorem weighted_recurrence (b c : ℤ) (m : ℕ) :
    weighted b c (m + 4) - 2 * weighted b c (m + 3) - weighted b c (m + 2) +
      2 * weighted b c (m + 1) + weighted b c m = 0 := by
  have h₂ : L (m + 2) = L (m + 1) + L m := rfl
  have h₃ : L (m + 3) = L (m + 2) + L (m + 1) := rfl
  have h₄ : L (m + 4) = L (m + 3) + L (m + 2) := rfl
  unfold weighted
  rw [h₄, h₃, h₂]
  push_cast
  ring

private theorem second_recurrence (m : ℕ) :
    second (m + 8) - 2 * second (m + 6) - second (m + 4) +
      2 * second (m + 2) + second m = 0 := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · have he : m = 2 * k := by omega
    have term (j : ℕ) : second (m + 2 * j) = weighted (-2) 1 (k + 1 + j) := by
      rw [show m + 2 * j = 2 * (k + j) by omega, second_even, weighted,
        show k + j + 1 = k + 1 + j by omega]
      push_cast
      ring
    have h := weighted_recurrence (-2) 1 (k + 1)
    rw [← term 4, ← term 3, ← term 2, ← term 1, ← term 0] at h
    simpa using h
  · have term (j : ℕ) : second (m + 2 * j) = weighted 2 1 (k + 2 + j) := by
      rw [show m + 2 * j = 2 * (k + j) + 1 by omega, second_odd, weighted,
        show k + j + 2 = k + 2 + j by omega]
      push_cast
      ring
    have h := weighted_recurrence 2 1 (k + 2)
    rw [← term 4, ← term 3, ← term 2, ← term 1, ← term 0] at h
    simpa using h

private theorem recurrence (n : ℕ) (hn : 10 ≤ n) :
    a n = 2 * a (n - 1) + a (n - 2) - 4 * a (n - 3) + 3 * a (n - 4) - 2 * a (n - 5) -
      a (n - 6) + 4 * a (n - 7) - 3 * a (n - 8) + 2 * a (n - 9) - a (n - 10) := by
  let m := n - 10
  have h := second_recurrence m
  unfold second at h
  simp only [Nat.add_assoc, Nat.reduceAdd] at h
  have index (j : ℕ) (hj : j ≤ 10) : m + j = n - (10 - j) := by
    dsimp [m]
    omega
  rw [index 10 (by decide), index 9 (by decide), index 8 (by decide),
    index 7 (by decide), index 6 (by decide), index 5 (by decide),
    index 4 (by decide), index 3 (by decide), index 2 (by decide), index 1 (by decide)] at h
  norm_num at h
  linarith

private theorem generating_function :
    (1 - X) ^ 2 * (1 - X ^ 2 - X ^ 4) ^ 2 * PowerSeries.mk a =
      (X * (3 - X + 9 * X ^ 2 - 7 * X ^ 3 - 5 * X ^ 4 - X ^ 5 - 2 * X ^ 6 - 2 * X ^ 7) :
        PowerSeries ℤ) := by
  let A : ℤ⟦X⟧ := mk a
  change (1 - X) ^ 2 * (1 - X ^ 2 - X ^ 4) ^ 2 * A = _
  have hC (k : ℕ) : C (k : ℤ) = (k : ℤ⟦X⟧) := map_natCast C k
  have hc₂ : C (2 : ℤ) = (2 : ℤ⟦X⟧) := hC 2
  have hc₃ : C (3 : ℤ) = (3 : ℤ⟦X⟧) := hC 3
  have hc₄ : C (4 : ℤ) = (4 : ℤ⟦X⟧) := hC 4
  have hc₅ : C (5 : ℤ) = (5 : ℤ⟦X⟧) := hC 5
  have hc₇ : C (7 : ℤ) = (7 : ℤ⟦X⟧) := hC 7
  have hc₉ : C (9 : ℤ) = (9 : ℤ⟦X⟧) := hC 9
  have hleft : (1 - X) ^ 2 * (1 - X ^ 2 - X ^ 4) ^ 2 * A =
      A - C 2 * (X ^ 1 * A) - X ^ 2 * A + C 4 * (X ^ 3 * A) - C 3 * (X ^ 4 * A) +
        C 2 * (X ^ 5 * A) + X ^ 6 * A - C 4 * (X ^ 7 * A) + C 3 * (X ^ 8 * A) -
        C 2 * (X ^ 9 * A) + X ^ 10 * A := by
    rw [hc₂, hc₃, hc₄]
    ring
  have hright : (X * (3 - X + 9 * X ^ 2 - 7 * X ^ 3 - 5 * X ^ 4 - X ^ 5 - 2 * X ^ 6 -
      2 * X ^ 7) : ℤ⟦X⟧) =
      C 3 * X - X ^ 2 + C 9 * X ^ 3 - C 7 * X ^ 4 - C 5 * X ^ 5 - X ^ 6 -
        C 2 * X ^ 7 - C 2 * X ^ 8 := by
    rw [hc₂, hc₃, hc₅, hc₇, hc₉]
    ring
  rw [hleft, hright]
  ext n
  by_cases hn : 10 ≤ n
  · have shift (j : ℕ) (hj : j ≤ 10) : coeff n (X ^ j * A) = a (n - j) := by
      rw [coeff_X_pow_mul', if_pos (by omega)]
      simp [A]
    have vanish (j : ℕ) (hj : j ≤ 8) : coeff n (X ^ j : ℤ⟦X⟧) = 0 := by
      simp [coeff_X_pow, show n ≠ j by omega]
    have vanishX : coeff n (X : ℤ⟦X⟧) = 0 := by simpa using vanish 1 (by decide)
    simp only [map_add, map_sub, coeff_C_mul, shift 1 (by decide), shift 2 (by decide),
      shift 3 (by decide), shift 4 (by decide), shift 5 (by decide), shift 6 (by decide),
      shift 7 (by decide), shift 8 (by decide), shift 9 (by decide), shift 10 (by decide),
      vanishX, vanish 2 (by decide), vanish 3 (by decide), vanish 4 (by decide),
      vanish 5 (by decide), vanish 6 (by decide), vanish 7 (by decide), vanish 8 (by decide),
      mul_zero, add_zero, sub_zero]
    simp only [A, coeff_mk]
    linarith [recurrence n hn]
  · have a₀ : a 0 = 0 := by decide
    have a₁ : a 1 = 3 := by decide
    have a₂ : a 2 = 5 := by decide
    have a₃ : a 3 = 22 := by decide
    have a₄ : a 4 = 30 := by decide
    have a₅ : a 5 = 66 := by decide
    have a₆ : a 6 = 82 := by decide
    have a₇ : a 7 = 161 := by decide
    have a₈ : a 8 = 191 := by decide
    have a₉ : a 9 = 342 := by decide
    interval_cases n <;>
      simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X, coeff_X_pow,
        A, coeff_mk] <;>
      norm_num [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉]

end A025093Proof

open A025093Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a025093.main :=
  ⟨fun n hn => recurrence n (by omega), generating_function⟩
