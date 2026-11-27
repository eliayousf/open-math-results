import OMAStatements.S_oeis_a203232
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace OpenMath.A203232

open OMA.S_oeis_a203232

private theorem step (n : ℕ) :
    products (n+1) = ((products n).1 * digit n,
      (products n).2 * digit n + (products n).1) := by
  change (let (p,e) := products n; (p * digit n, e * digit n + p)) = _
  cases products n; rfl

private theorem block (n : ℕ) :
    products (n+2) = (6 * (products n).1,
      6 * (products n).2 + 5 * (products n).1) := by
  rw [step (n+1), step n]
  simp only [digit]
  have h1 : (n+1) % 2 = (n % 2 + 1) % 2 := by omega
  rw [h1]
  have hr : n % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize n % 2 = r at hr ⊢
  interval_cases r <;> apply Prod.ext <;> norm_num <;> ring

private theorem shift_recur (n : ℕ) :
    a (n+4) = 12 * a (n+2) - 36 * a n := by
  unfold a
  rw [show n+4 = (n+2)+2 by omega, block (n+2), block n]
  dsimp
  ring

open PowerSeries

theorem generating_function :
    (1 - C 6 * X^2 : ℤ⟦X⟧)^2 * mk a = X^1 + C 5 * X^2 + C 4 * X^3 := by
  have hden : (1 - C 6 * X^2 : ℤ⟦X⟧)^2 =
      1 - C 12 * X^2 + C 36 * X^4 := by
    simp
    ring
  rw [hden]
  ext n
  simp only [add_mul, sub_mul, one_mul, map_add, map_sub, mul_assoc, coeff_mk,
    coeff_C_mul, coeff_X_pow_mul', coeff_X_pow]
  by_cases hn : n < 4
  · interval_cases n <;> decide
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+4 := ⟨n-4, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), show k+4-2 = k+2 by omega,
      show k+4-4 = k by omega, shift_recur]
    split_ifs <;> omega

theorem main :
    (∀ n : ℕ, 4 < n → a n = 12 * a (n-2) - 36 * a (n-4)) ∧
    ((1 - C 6 * X^2 : ℤ⟦X⟧)^2 * mk a = X^1 + C 5 * X^2 + C 4 * X^3) := by
  refine ⟨?_, generating_function⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+4 := ⟨n-4, by omega⟩
  rw [show k+4-2 = k+2 by omega, show k+4-4 = k by omega]
  exact shift_recur k

end OpenMath.A203232

theorem OMA.solution : type_of% @OMA.S_oeis_a203232.main := OpenMath.A203232.main
