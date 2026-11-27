import OMAStatements.S_oeis_a024385
import Mathlib.Data.Int.DivMod
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OpenMath.A024385

open OMA.S_oeis_a024385 (stats a)

private def poly (x : ℤ) : ℤ := 6*x^2 - 11*x + 2

private theorem first_eq (m : ℕ) :
    (stats m).1 = (m : ℤ) * (2 * (m : ℤ) - 1) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [stats, Nat.cast_succ]
    change (stats m).1 + (4*(m:ℤ)+1) = ((m:ℤ)+1)*(2*((m:ℤ)+1)-1)
    linear_combination ih

private theorem second_eq (m : ℕ) :
    6 * (stats m).2 = (stats m).1 * poly m + 3 * (m : ℤ) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [stats, Nat.cast_succ]
    change 6*((stats m).2+(4*(m:ℤ)+1)*(stats m).1) =
      ((stats m).1+(4*(m:ℤ)+1))*poly ((m:ℤ)+1)+3*((m:ℤ)+1)
    unfold poly at ih ⊢
    linear_combination ih + (12*(m:ℤ)+11)*first_eq m

private theorem ratio (m : ℕ) (hm : 3 ≤ m) :
    (stats m).2 / (stats m).1 = poly m / 6 := by
  let u := (stats m).1
  have hmR : (3 : ℤ) ≤ m := by exact_mod_cast hm
  have hu : 3 * (m : ℤ) < u := by
    change _ < (stats m).1
    rw [first_eq]
    calc
      3*(m:ℤ) < (m:ℤ)*5 := by omega
      _ ≤ _ := mul_le_mul_of_nonneg_left (by omega) (by omega)
  have hpos : 0 < u := by omega
  have hsplit : poly m = 6*(poly m / 6) + poly m % 6 := by omega
  have hs := congrArg (fun z : ℤ => u*z) hsplit
  have he := second_eq m
  have hlo : 0 ≤ poly m % 6 := by omega
  have hhi : poly m % 6 ≤ 5 := by omega
  have hl := mul_nonneg hpos.le hlo
  have hh := mul_le_mul_of_nonneg_left hhi hpos.le
  change (stats m).2 / u = poly m / 6
  apply (Int.ediv_eq_iff_of_pos hpos).mpr
  constructor
  · dsimp [u] at hs hl ⊢
    nlinarith only [he,hs,hl,hmR]
  · dsimp [u] at hs hh hu ⊢
    nlinarith only [he,hs,hh,hu]

private theorem closed (n : ℕ) (hn : 1 ≤ n) :
    a n = (n : ℤ)^2 + ((n : ℤ) - 3) / 6 := by
  by_cases he : n = 1
  · subst n
    decide
  rw [a, if_neg (by omega), ratio (n+1) (by omega)]
  rw [show poly ((n+1 : ℕ) : ℤ) = 6*(n:ℤ)^2 + ((n:ℤ)-3) by
    unfold poly
    push_cast
    ring]
  omega

private theorem shift (n : ℕ) (hn : 1 ≤ n) : a (n+6) = a n + 12*(n : ℤ) + 37 := by
  rw [closed _ (by omega), closed _ hn]
  push_cast
  rw [show ((n:ℤ)+6-3)/6=((n:ℤ)-3)/6+1 by omega]
  ring

theorem recurrence (n : ℕ) (hn : 9 ≤ n) :
    a n = 2*a (n-1) - a (n-2) + a (n-6) - 2*a (n-7) + a (n-8) := by
  have h1 := shift (n-6) (by omega)
  have h2 := shift (n-7) (by omega)
  have h3 := shift (n-8) (by omega)
  rw [show n-6+6=n by omega, Nat.cast_sub (by omega : 6≤n)] at h1
  rw [show n-7+6=n-1 by omega, Nat.cast_sub (by omega : 7≤n)] at h2
  rw [show n-8+6=n-2 by omega, Nat.cast_sub (by omega : 8≤n)] at h3
  norm_num at h1 h2 h3
  omega

open PowerSeries in
theorem generating_function :
    (1-X)^2*(1-X^6) * mk a =
      3*X^2+3*X^3+X^4+2*X^5+2*X^6+2*X^7-X^8 := by
  have hd : ((1-X)^2*(1-X^6) : ℤ⟦X⟧) =
      1 - C 2*X^1 + X^2 - X^6 + C 2*X^7 - X^8 := by
    simp
    ring
  have hp : (3*X^2+3*X^3+X^4+2*X^5+2*X^6+2*X^7-X^8 : ℤ⟦X⟧) =
      C 3*X^2+C 3*X^3+X^4+C 2*X^5+C 2*X^6+C 2*X^7-X^8 := by simp
  rw [hd, hp]
  ext n
  simp only [sub_mul, add_mul, one_mul, map_add, map_sub, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n < 9
  · interval_cases n <;> decide
  · simp [show 1≤n by omega, show 2≤n by omega, show 6≤n by omega,
      show 7≤n by omega, show 8≤n by omega, show n≠2 by omega, show n≠3 by omega,
      show n≠4 by omega, show n≠5 by omega, show n≠6 by omega, show n≠7 by omega,
      show n≠8 by omega]
    have h := recurrence n (by omega)
    omega

open PowerSeries in
theorem main :
    (∀ n ≥ 9, a n = 2*a (n-1) - a (n-2) + a (n-6) - 2*a (n-7) + a (n-8)) ∧
    ((1-X)^2*(1-X^6) * mk a = 3*X^2+3*X^3+X^4+2*X^5+2*X^6+2*X^7-X^8) :=
  ⟨recurrence, generating_function⟩

end OpenMath.A024385

theorem OMA.solution : type_of% @OMA.S_oeis_a024385.main := OpenMath.A024385.main
