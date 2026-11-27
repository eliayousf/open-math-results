import OMAStatements.S_oeis_a230113
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace OpenMath.A230113

open OMA.S_oeis_a230113

private theorem input_pos (n : ℕ) : 0 < input n := by
  unfold input
  have h : ∀ i : Fin 8, 0 < residue i := by decide
  have h' := h ⟨n % 8, Nat.mod_lt _ (by decide)⟩
  omega

private theorem input_period (n : ℕ) : input (n + 32) = input n + 120 := by
  unfold input
  rw [show (n + 32) / 8 = n / 8 + 4 by omega]
  have hr : (⟨(n + 32) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) =
      ⟨n % 8, Nat.mod_lt _ (by decide)⟩ :=
    Fin.ext (by dsimp; omega)
  rw [hr]
  omega

private def residues (u v n : ℕ) : ℕ × ℕ :=
  ((consecutive u v n).1 % 9, (consecutive u v n).2 % 9)

private theorem residues_step (u v n : ℕ) :
    residues u v (n + 1) =
      ((residues u v n).2, ((residues u v n).1 + (residues u v n).2) % 9) := by
  change ((consecutive u v n).2 % 9, ((consecutive u v n).1 + (consecutive u v n).2) % 9) =
    ((consecutive u v n).2 % 9, ((consecutive u v n).1 % 9 + (consecutive u v n).2 % 9) % 9)
  rw [Nat.add_mod (consecutive u v n).1 (consecutive u v n).2 9]

private theorem residues_period (u v : ℕ)
    (h : residues u v 120 = residues u v 0) (n : ℕ) :
    residues u v (n + 120) = residues u v n := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [show n + 1 + 120 = n + 120 + 1 by omega,
      residues_step u v (n + 120), residues_step u v n, ih]

private theorem second_pos (u v : ℕ) (hv : 0 < v) (n : ℕ) :
    0 < (consecutive u v n).2 := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    change 0 < (consecutive u v n).1 + (consecutive u v n).2
    omega

private theorem fib_pos (n : ℕ) (hn : 0 < n) : 0 < fib n := by
  cases n with
  | zero => omega
  | succ n => exact second_pos 0 1 (by decide) n

private theorem lucas_pos (n : ℕ) : 0 < lucas n := by
  cases n with
  | zero => decide
  | succ n => exact second_pos 2 1 (by decide) n

private theorem root_eq (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (h : x % 9 = y % 9) :
    root x = root y := by
  simp [root, hx.ne', hy.ne', h]

private theorem term_period (n : ℕ) : term (n + 32) = term n := by
  have hn := input_pos n
  have hf := congrArg Prod.fst (residues_period 0 1 (by decide) (input n))
  have hl := congrArg Prod.fst (residues_period 2 1 (by decide) (input n - 1))
  change fib (input n + 120) % 9 = fib (input n) % 9 at hf
  change lucas (input n - 1 + 120) % 9 = lucas (input n - 1) % 9 at hl
  unfold term
  rw [input_period, show input n + 120 - 1 = input n - 1 + 120 by omega]
  rw [root_eq _ _ (fib_pos _ (by omega)) (fib_pos _ hn) hf,
    root_eq _ _ (lucas_pos _) (lucas_pos _) hl]

private theorem term_mod (n : ℕ) : term n = term (n % 32) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 32
    · rw [Nat.mod_eq_of_lt hn]
    · conv_lhs => rw [show n = (n - 32) + 32 by omega, term_period]
      rw [ih (n - 32) (by omega), show (n - 32) % 32 = n % 32 by omega]

private theorem term_complement (n : ℕ) : term (n + 16) + term n = 9 := by
  rw [term_mod (n + 16), term_mod n, show (n + 16) % 32 = (n % 32 + 16) % 32 by omega]
  have h : n % 32 < 32 := Nat.mod_lt _ (by decide)
  generalize n % 32 = k at h ⊢
  interval_cases k <;> decide

theorem recurrence (n : ℕ) (hn : 17 < n) :
    a n = a (n - 1) - a (n - 16) + a (n - 17) := by
  let k := n - 18
  have h1 := term_complement (k + 1)
  rw [show k + 1 + 16 = k + 17 by omega] at h1
  have h0 := term_complement k
  rw [show n = k + 17 + 1 by omega, show k + 17 + 1 - 1 = k + 16 + 1 by omega,
    show k + 17 + 1 - 16 = k + 1 + 1 by omega,
    show k + 17 + 1 - 17 = k + 1 by omega]
  simp only [a]
  omega


open PowerSeries

theorem generating_function :
    ((1-X : ℤ⟦X⟧) * (1+X^16)) * mk a =
      C 3 * X^1 + X^2 + X^3 + X^4 - X^6 - X^7 - X^8 + X^9 + C 2 * X^10 -
        X^12 - X^13 - X^14 + C 2 * X^16 + C 4 * X^17 := by
  have hden : ((1-X : ℤ⟦X⟧) * (1+X^16)) = 1-X^1+X^16-X^17 := by
    simp
    ring
  rw [hden]
  ext n
  simp only [sub_mul, add_mul, one_mul, map_sub, map_add, coeff_mk,
    coeff_X_pow_mul', coeff_C_mul, coeff_X_pow]
  by_cases hn : n ≤ 17
  · interval_cases n <;> decide
  · have hgt : 17 < n := by omega
    have hne (k : ℕ) (hk : k ≤ 17) : n ≠ k := by omega
    simp only [if_pos (show 1 ≤ n by omega), if_pos (show 16 ≤ n by omega),
      if_pos (show 17 ≤ n by omega),
      if_neg (hne 1 (by decide)), if_neg (hne 2 (by decide)),
      if_neg (hne 3 (by decide)), if_neg (hne 4 (by decide)),
      if_neg (hne 6 (by decide)), if_neg (hne 7 (by decide)),
      if_neg (hne 8 (by decide)), if_neg (hne 9 (by decide)),
      if_neg (hne 10 (by decide)), if_neg (hne 12 (by decide)),
      if_neg (hne 13 (by decide)), if_neg (hne 14 (by decide)),
      if_neg (hne 16 (by decide)), if_neg (hne 17 (by decide))]
    have hr := recurrence n hgt
    omega

theorem main :
    (∀ n : ℕ, 17 < n → a n = a (n-1) - a (n-16) + a (n-17)) ∧
    (((1-X : ℤ⟦X⟧) * (1+X^16)) * mk a =
      C 3 * X^1 + X^2 + X^3 + X^4 - X^6 - X^7 - X^8 + X^9 + C 2 * X^10 -
        X^12 - X^13 - X^14 + C 2 * X^16 + C 4 * X^17) := by
  exact ⟨recurrence, generating_function⟩

end OpenMath.A230113

theorem OMA.solution : type_of% @OMA.S_oeis_a230113.main := OpenMath.A230113.main
