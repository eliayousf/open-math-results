import OMAStatements.S_oeis_a401159
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OpenMath.A401159

open OMA.S_oeis_a401159

private def scaledPolynomial (x : ℤ) : ℕ → ℕ → ℤ
  | 0, 0 => 8
  | 0, 1 => 8 + 8*x
  | 0, 2 => 8 + 16*x + 8*x^2
  | 0, 3 => 8 + 16*x + 24*x^2 + 8*x^3
  | 1, 0 => 8 + 4*x + 4*x^2
  | 1, 1 => 8 + 12*x + 8*x^2 + 4*x^3
  | 1, 2 => 8 + 20*x + 12*x^2 + 12*x^3 + 4*x^4
  | 2, 0 => 8 + 8*x + 10*x^2 + 4*x^3 + 2*x^4
  | 2, 1 => 8 + 16*x + 18*x^2 + 6*x^3 + 6*x^4 + 2*x^5
  | 3, 0 => 8 + 8*x + 22*x^2 + 13*x^3 + x^4 + 3*x^5 + x^6
  | _, _ => 0

private theorem push_scale (c x : ℤ) : 8 * (c * x) = c * (8 * x) := by ring

private theorem polynomial_correct (n : ℕ) :
    ∀ d s : ℕ, d+s ≤ 3 → 8 * remaining n d s = scaledPolynomial n d s := by
  induction n with
  | zero =>
    intro d s h
    have hd : d ≤ 3 := by omega
    have hs : s ≤ 3 := by omega
    interval_cases d <;> interval_cases s <;> first | omega | decide
  | succ n ih =>
    intro d s h
    have hd : d ≤ 3 := by omega
    have hs : s ≤ 3 := by omega
    interval_cases d <;> interval_cases s <;> try omega
    all_goals
      simp only [remaining, Nat.cast_succ, mul_add, push_scale]
      norm_num [Nat.choose, ih, scaledPolynomial] <;> ring

theorem column_three (n : ℕ) :
    8 * T n 3 = 8 + 8*(n : ℤ) + 22*(n : ℤ)^2 + 13*(n : ℤ)^3
      + (n : ℤ)^4 + 3*(n : ℤ)^5 + (n : ℤ)^6 :=
  polynomial_correct n 3 0 (by decide)

end OpenMath.A401159

theorem OMA.solution : type_of% @OMA.S_oeis_a401159.main :=
  OpenMath.A401159.column_three
