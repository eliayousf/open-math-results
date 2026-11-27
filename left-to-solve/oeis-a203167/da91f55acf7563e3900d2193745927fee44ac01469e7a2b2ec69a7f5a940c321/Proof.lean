import OMAStatements.S_oeis_a203167
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace OpenMath.A203167

open OMA.S_oeis_a203167

private theorem step (n : ℕ) :
    products (n+1) = ((products n).1 * digit n,
      (products n).2 * digit n + (products n).1) := by
  change (let (p,e) := products n; (p * digit n, e * digit n + p)) = _
  cases products n; rfl

private theorem block (n : ℕ) :
    products (n+3) = (4 * (products n).1,
      4 * (products n).2 + 8 * (products n).1) := by
  rw [step (n+2), step (n+1), step n]
  simp only [digit]
  have h1 : (n+1) % 3 = (n % 3 + 1) % 3 := by omega
  have h2 : (n+2) % 3 = (n % 3 + 2) % 3 := by omega
  rw [h1]
  rw [h2]
  have hr : n % 3 < 3 := Nat.mod_lt _ (by decide)
  generalize n % 3 = r at hr ⊢
  interval_cases r <;> apply Prod.ext <;> norm_num <;> ring

private theorem shift_recur (n : ℕ) :
    a (n+6) = 8 * a (n+3) - 16 * a n := by
  unfold a
  rw [show n+6 = (n+3)+3 by omega, block (n+3), block n]
  dsimp
  ring

open PowerSeries

theorem generating_function :
    (1 - C 4 * X^3 : ℤ⟦X⟧)^2 * mk a = X^1 + C 4 * X^2 + C 8 * X^3 + C 12 * X^4 + C 16 * X^5 := by
  have hden : (1 - C 4 * X^3 : ℤ⟦X⟧)^2 =
      1 - C 8 * X^3 + C 16 * X^6 := by
    simp
    ring
  rw [hden]
  ext n
  simp only [add_mul, sub_mul, one_mul, map_add, map_sub, mul_assoc, coeff_mk,
    coeff_C_mul, coeff_X_pow_mul', coeff_X_pow]
  by_cases hn : n < 6
  · interval_cases n <;> decide
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+6 := ⟨n-6, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), show k+6-3 = k+3 by omega,
      show k+6-6 = k by omega, shift_recur]
    split_ifs <;> omega

theorem main :
    (∀ n : ℕ, 6 < n → a n = 8 * a (n-3) - 16 * a (n-6)) ∧
    ((1 - C 4 * X^3 : ℤ⟦X⟧)^2 * mk a = X^1 + C 4 * X^2 + C 8 * X^3 + C 12 * X^4 + C 16 * X^5) := by
  refine ⟨?_, generating_function⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+6 := ⟨n-6, by omega⟩
  rw [show k+6-3 = k+3 by omega, show k+6-6 = k by omega]
  exact shift_recur k

end OpenMath.A203167

theorem OMA.solution : type_of% @OMA.S_oeis_a203167.main := OpenMath.A203167.main
