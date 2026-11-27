import OMAStatements.S_oeis_a203150
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace OpenMath.A203150

open OMA.S_oeis_a203150

private theorem step (n : ℕ) :
    products (n+1) = ((products n).1 * digit n,
      (products n).2 * digit n + (products n).1) := by
  change (let (p,e) := products n; (p * digit n, e * digit n + p)) = _
  cases products n; rfl

private theorem block (k : ℕ) :
    products (2*k+2) = (2 * (products (2*k)).1,
      2 * a (2*k) + 3 * (products (2*k)).1) := by
  rw [step (2*k+1), step (2*k)]
  simp only [digit, show 2*k % 2 = 0 by omega, show (2*k+1) % 2 = 1 by omega,
    if_true, Nat.one_ne_zero, if_false, a]
  apply Prod.ext <;> dsimp <;> ring

private theorem even_stats (k : ℕ) :
    (products (2*k)).1 = 2^k ∧ 2 * a (2*k) = 3 * (k : ℤ) * 2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hf := congrArg Prod.fst (block k)
    have he := congrArg Prod.snd (block k)
    change (products (2*k+2)).1 = 2 * (products (2*k)).1 at hf
    change a (2*k+2) = 2 * a (2*k) + 3 * (products (2*k)).1 at he
    rw [show 2*(k+1) = 2*k+2 by omega, Nat.cast_succ, pow_succ]
    constructor
    · rw [hf, ih.1]; ring
    · rw [he, ih.1]
      linear_combination 2 * ih.2

private theorem odd_stats (k : ℕ) :
    2 * a (2*k+1) = (3 * (k : ℤ) + 2) * 2^k := by
  unfold a at *
  rw [step]
  simp only [digit, show 2*k % 2 = 0 by omega, if_true, mul_one]
  have hp := (even_stats k).1
  have he := (even_stats k).2
  unfold a at he
  rw [hp]
  linear_combination he

theorem main : ∀ n : ℕ, 0 < n →
    let r := Real.sqrt 2
    (a n : ℝ) =
      (6 * r * (n : ℝ) + (1 + 3 * (1-r) * (n : ℝ)) * (1 - (-1 : ℝ)^n)) *
        r^(n-1) / 8 := by
  intro n hn
  dsimp
  let r := Real.sqrt 2
  change (a n : ℝ) = (6 * r * (n : ℝ) + (1 + 3 * (1-r) * (n : ℝ)) *
    (1 - (-1 : ℝ)^n)) * r^(n-1) / 8
  have hsq : r^2 = 2 := Real.sq_sqrt (by norm_num)
  obtain he | ho : n = 2*(n/2) ∨ n = 2*(n/2)+1 := by omega
  · let k := n/2
    have he' : n = 2*k := he
    have hs : (2 : ℝ) * (a (2*k) : ℝ) = 3 * (k : ℝ) * 2^k := by
      exact_mod_cast (even_stats k).2
    have hsign : (-1 : ℝ)^(2*k) = 1 := by rw [pow_mul]; norm_num
    have hpow : r * r^(2*k-1) = (2 : ℝ)^k := calc
      r * r^(2*k-1) = r^(2*k-1+1) := by rw [pow_succ]; ring
      _ = r^(2*k) := by rw [show 2*k-1+1 = 2*k by omega]
      _ = 2^k := by rw [pow_mul, hsq]
    rw [he', hsign]
    push_cast
    rw [show (6*r*(2*(k : ℝ)) + (1+3*(1-r)*(2*(k : ℝ)))*(1-1))*r^(2*k-1) =
        12*(k : ℝ)*(r*r^(2*k-1)) by ring, hpow]
    linear_combination hs / 2
  · let k := n/2
    have ho' : n = 2*k+1 := ho
    have hs : (2 : ℝ) * (a (2*k+1) : ℝ) = (3 * (k : ℝ) + 2) * 2^k := by
      exact_mod_cast odd_stats k
    have hsign : (-1 : ℝ)^(2*k+1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have hpow : r^(2*k+1-1) = (2 : ℝ)^k := by
      rw [show 2*k+1-1 = 2*k by omega, pow_mul, hsq]
    rw [ho', hsign, hpow]
    push_cast
    linear_combination hs / 2

end OpenMath.A203150

theorem OMA.solution : type_of% @OMA.S_oeis_a203150.main := OpenMath.A203150.main
