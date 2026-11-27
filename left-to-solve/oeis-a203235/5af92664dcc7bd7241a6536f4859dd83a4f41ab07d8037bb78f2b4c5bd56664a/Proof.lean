import OMAStatements.S_oeis_a203235
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace OpenMath.A203235

open OMA.S_oeis_a203235

private theorem step (n : ℕ) :
    products (n+1) = ((products n).1 * digit n,
      (products n).2 * digit n + (products n).1) := by
  change (let (p,e) := products n; (p * digit n, e * digit n + p)) = _
  cases products n; rfl

private theorem block (n : ℕ) :
    products (n+4) = (3 * (products n).1,
      3 * (products n).2 + 10 * (products n).1) := by
  rw [step (n+3), step (n+2), step (n+1), step n]
  simp only [digit]
  have h1 : (n+1) % 4 = (n % 4 + 1) % 4 := by omega
  have h2 : (n+2) % 4 = (n % 4 + 2) % 4 := by omega
  have h3 : (n+3) % 4 = (n % 4 + 3) % 4 := by omega
  rw [h1]
  rw [h2]
  rw [h3]
  have hr : n % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize n % 4 = r at hr ⊢
  interval_cases r <;> apply Prod.ext <;> norm_num <;> ring

private theorem shift_recur (n : ℕ) :
    a (n+8) = 6 * a (n+4) - 9 * a n := by
  unfold a
  rw [show n+8 = (n+4)+4 by omega, block (n+4), block n]
  dsimp
  ring

open PowerSeries

theorem generating_function :
    (1 - C 3 * X^4 : ℤ⟦X⟧)^2 * mk a = X^1 + C 2 * X^2 + C 3 * X^3 + C 10 * X^4 + C 7 * X^5 + C 4 * X^6 + X^7 := by
  have hden : (1 - C 3 * X^4 : ℤ⟦X⟧)^2 =
      1 - C 6 * X^4 + C 9 * X^8 := by
    simp
    ring
  rw [hden]
  ext n
  simp only [add_mul, sub_mul, one_mul, map_add, map_sub, mul_assoc, coeff_mk,
    coeff_C_mul, coeff_X_pow_mul', coeff_X_pow]
  by_cases hn : n < 8
  · interval_cases n <;> decide
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+8 := ⟨n-8, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), show k+8-4 = k+4 by omega,
      show k+8-8 = k by omega, shift_recur]
    split_ifs <;> omega

theorem main :
    (∀ n : ℕ, 8 < n → a n = 6 * a (n-4) - 9 * a (n-8)) ∧
    ((1 - C 3 * X^4 : ℤ⟦X⟧)^2 * mk a = X^1 + C 2 * X^2 + C 3 * X^3 + C 10 * X^4 + C 7 * X^5 + C 4 * X^6 + X^7) := by
  refine ⟨?_, generating_function⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+8 := ⟨n-8, by omega⟩
  rw [show k+8-4 = k+4 by omega, show k+8-8 = k by omega]
  exact shift_recur k

end OpenMath.A203235

theorem OMA.solution : type_of% @OMA.S_oeis_a203235.main := OpenMath.A203235.main
