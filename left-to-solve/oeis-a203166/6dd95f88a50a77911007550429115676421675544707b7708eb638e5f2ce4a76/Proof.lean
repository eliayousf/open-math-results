import OMAStatements.S_oeis_a203166
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace OpenMath.A203166

open OMA.S_oeis_a203166

private theorem step (n : ℕ) :
    products (n+1) = ((products n).1 * digit n,
      (products n).2 * digit n + (products n).1) := by
  change (let (p,e) := products n; (p * digit n, e * digit n + p)) = _
  cases products n; rfl

private theorem block (n : ℕ) :
    products (n+5) = (120 * (products n).1,
      120 * (products n).2 + 274 * (products n).1) := by
  rw [step (n+4), step (n+3), step (n+2), step (n+1), step n]
  simp only [digit]
  have h1 : (n+1) % 5 = (n % 5 + 1) % 5 := by omega
  have h2 : (n+2) % 5 = (n % 5 + 2) % 5 := by omega
  have h3 : (n+3) % 5 = (n % 5 + 3) % 5 := by omega
  have h4 : (n+4) % 5 = (n % 5 + 4) % 5 := by omega
  rw [h1]
  rw [h2]
  rw [h3]
  rw [h4]
  have hr : n % 5 < 5 := Nat.mod_lt _ (by decide)
  generalize n % 5 = r at hr ⊢
  interval_cases r <;> apply Prod.ext <;> norm_num <;> ring

private theorem shift_recur (n : ℕ) :
    a (n+10) = 240 * a (n+5) - 14400 * a n := by
  unfold a
  rw [show n+10 = (n+5)+5 by omega, block (n+5), block n]
  dsimp
  ring

open PowerSeries

theorem generating_function :
    (1 - C 120 * X^5 : ℤ⟦X⟧)^2 * mk a = X^1 + C 3 * X^2 + C 11 * X^3 + C 50 * X^4 + C 274 * X^5 + C 154 * X^6 + C 188 * X^7 + C 324 * X^8 + C 576 * X^9 := by
  have hden : (1 - C 120 * X^5 : ℤ⟦X⟧)^2 =
      1 - C 240 * X^5 + C 14400 * X^10 := by
    simp
    ring
  rw [hden]
  ext n
  simp only [add_mul, sub_mul, one_mul, map_add, map_sub, mul_assoc, coeff_mk,
    coeff_C_mul, coeff_X_pow_mul', coeff_X_pow]
  by_cases hn : n < 10
  · interval_cases n <;> decide
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+10 := ⟨n-10, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), show k+10-5 = k+5 by omega,
      show k+10-10 = k by omega, shift_recur]
    split_ifs <;> omega

theorem main :
    (∀ n : ℕ, 10 < n → a n = 240 * a (n-5) - 14400 * a (n-10)) ∧
    ((1 - C 120 * X^5 : ℤ⟦X⟧)^2 * mk a = X^1 + C 3 * X^2 + C 11 * X^3 + C 50 * X^4 + C 274 * X^5 + C 154 * X^6 + C 188 * X^7 + C 324 * X^8 + C 576 * X^9) := by
  refine ⟨?_, generating_function⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+10 := ⟨n-10, by omega⟩
  rw [show k+10-5 = k+5 by omega, show k+10-10 = k by omega]
  exact shift_recur k

end OpenMath.A203166

theorem OMA.solution : type_of% @OMA.S_oeis_a203166.main := OpenMath.A203166.main
