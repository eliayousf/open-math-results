import OMAStatements.S_oeis_a024220
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

namespace OpenMath.A024220

open OMA.S_oeis_a024220 (e a)

private def poly (m : ℤ) : ℤ :=
  9 * m ^ 4 - 42 * m ^ 3 + 55 * m ^ 2 - 6 * m - 16

private theorem e1 (m : ℕ) : 2 * e m 1 = 3 * (m : ℤ) ^ 2 - m := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [e, show e m 0 = 1 by cases m <;> rfl, Nat.cast_succ]
    linear_combination ih

private theorem e2 (m : ℕ) :
    8 * e m 2 = 9 * (m : ℤ) ^ 4 - 18 * (m : ℤ) ^ 3 + 7 * (m : ℤ) ^ 2 + 2 * m := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [e, Nat.cast_succ]
    linear_combination ih + 4 * (3 * (m : ℤ) + 1) * e1 m

private theorem e3 (m : ℕ) :
    48 * e m 3 = (3 * (m : ℤ) ^ 2 - m) * poly m := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [e, Nat.cast_succ]
    unfold poly at ih ⊢
    linear_combination ih + 6 * (3 * (m : ℤ) + 1) * e2 m

private theorem e1_pos (m : ℕ) (hm : 1 ≤ m) : 0 < e m 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h := e1 (k + 1)
  push_cast at h
  have h0 : (0 : ℤ) ≤ k := by positivity
  nlinarith only [h, h0, sq_nonneg (k : ℤ)]

private theorem ratio (m : ℕ) :
    e m 1 * poly m = 24 * e m 3 := by
  have h : 2 * (e m 1 * poly m) = 2 * (24 * e m 3) := by
    linear_combination poly m * e1 m - e3 m
  omega

private theorem a_eq (n : ℕ) : a n = poly (↑n + 2) / 24 := by
  unfold a
  have hpos := e1_pos (n + 2) (by omega)
  have h := ratio (n + 2)
  push_cast at h
  have h0 : 24 * (poly (↑n + 2) / 24) + poly (↑n + 2) % 24 = poly (↑n + 2) := by omega
  have hs := congrArg (fun x : ℤ => e (n + 2) 1 * x) h0
  have h1 := Int.emod_nonneg (poly (↑n + 2)) (by decide : (24 : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos (poly (↑n + 2)) (by decide : (0 : ℤ) < 24)
  apply (Int.ediv_eq_iff_of_pos hpos).2
  constructor
  · have he := mul_nonneg hpos.le h1
    nlinarith only [h, hs, he]
  · have he := mul_pos hpos (show 0 < 24 - poly (↑n + 2) % 24 by omega)
    nlinarith only [h, hs, he]

private theorem residue (m : ℤ) : poly m % 24 = if m % 3 = 0 then 8 else 0 := by
  have hm : m ≡ m % 24 [ZMOD 24] := by
    unfold Int.ModEq
    omega
  have hp : poly m ≡ poly (m % 24) [ZMOD 24] := by
    unfold poly
    exact (((((hm.pow 4).mul_left 9).sub ((hm.pow 3).mul_left 42)).add
      ((hm.pow 2).mul_left 55)).sub (hm.mul_left 6)).sub_right 16
  rw [hp.eq, ← show (m % 24) % 3 = m % 3 by omega]
  have hl : 0 ≤ m % 24 := by omega
  have hu : m % 24 < 24 := by omega
  generalize m % 24 = r at hl hu ⊢
  interval_cases r <;> decide

private theorem scaled (n : ℕ) :
    24 * a n = poly (↑n + 2) - (if (↑n + 2 : ℤ) % 3 = 0 then 8 else 0) := by
  rw [a_eq, ← residue]
  omega

private theorem linear (k : ℕ) :
    a (k + 7) = 4 * a (k + 6) - 6 * a (k + 5) + 5 * a (k + 4) -
      5 * a (k + 3) + 6 * a (k + 2) - 4 * a (k + 1) + a k := by
  have h0 := scaled k
  have h1 := scaled (k + 1)
  have h2 := scaled (k + 2)
  have h3 := scaled (k + 3)
  have h4 := scaled (k + 4)
  have h5 := scaled (k + 5)
  have h6 := scaled (k + 6)
  have h7 := scaled (k + 7)
  simp only [Nat.cast_add, Nat.cast_ofNat] at h1 h2 h3 h4 h5 h6 h7
  rw [show ((k : ℤ) + 3 + 2) % 3 = (↑k + 2) % 3 by omega] at h3
  rw [show ((k : ℤ) + 4 + 2) % 3 = (↑k + 1 + 2) % 3 by omega] at h4
  rw [show ((k : ℤ) + 5 + 2) % 3 = (↑k + 2 + 2) % 3 by omega] at h5
  rw [show ((k : ℤ) + 6 + 2) % 3 = (↑k + 2) % 3 by omega] at h6
  rw [show ((k : ℤ) + 7 + 2) % 3 = (↑k + 1 + 2) % 3 by omega] at h7
  unfold poly at h0 h1 h2 h3 h4 h5 h6 h7
  have h :
      24 * (a (k + 7) - 4 * a (k + 6) + 6 * a (k + 5) - 5 * a (k + 4) +
        5 * a (k + 3) - 6 * a (k + 2) + 4 * a (k + 1) - a k) = 0 := by
    linear_combination h7 - 4 * h6 + 6 * h5 - 5 * h4 + 5 * h3 - 6 * h2 + 4 * h1 - h0
  omega


open PowerSeries in
theorem generating_function :
    (1 - X) ^ 4 * (1 - X ^ 3) * mk a = 2 * X + 11 * X ^ 2 + 7 * X ^ 3 + 8 * X ^ 4 - X ^ 5 := by
  have hden : ((1 - X) ^ 4 * (1 - X ^ 3) : ℤ⟦X⟧) =
      1 - C 4 * X ^ 1 + C 6 * X ^ 2 - C 5 * X ^ 3 + C 5 * X ^ 4 -
        C 6 * X ^ 5 + C 4 * X ^ 6 - X ^ 7 := by
    simp
    ring
  have hnum : (2 * X + 11 * X ^ 2 + 7 * X ^ 3 + 8 * X ^ 4 - X ^ 5 : ℤ⟦X⟧) =
      C 2 * X ^ 1 + C 11 * X ^ 2 + C 7 * X ^ 3 + C 8 * X ^ 4 - X ^ 5 := by simp
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n < 7
  · interval_cases n <;> decide
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  simp only [if_pos (show 1 ≤ k + 7 by omega), if_pos (show 2 ≤ k + 7 by omega),
    if_pos (show 3 ≤ k + 7 by omega), if_pos (show 4 ≤ k + 7 by omega),
    if_pos (show 5 ≤ k + 7 by omega), if_pos (show 6 ≤ k + 7 by omega),
    if_pos (show 7 ≤ k + 7 by omega), if_neg (show k + 7 ≠ 1 by omega),
    if_neg (show k + 7 ≠ 2 by omega), if_neg (show k + 7 ≠ 3 by omega),
    if_neg (show k + 7 ≠ 4 by omega), if_neg (show k + 7 ≠ 5 by omega)]
  change a (k + 7) - 4 * a (k + 6) + 6 * a (k + 5) - 5 * a (k + 4) +
    5 * a (k + 3) - 6 * a (k + 2) + 4 * a (k + 1) - a k = _
  have h := linear k
  omega

open PowerSeries in
theorem main :
    (∀ n : ℕ, 8 ≤ n → a n = 4 * a (n - 1) - 6 * a (n - 2) + 5 * a (n - 3) -
      5 * a (n - 4) + 6 * a (n - 5) - 4 * a (n - 6) + a (n - 7)) ∧
    ((1 - X) ^ 4 * (1 - X ^ 3) * mk a = 2 * X + 11 * X ^ 2 + 7 * X ^ 3 + 8 * X ^ 4 - X ^ 5) := by
  refine ⟨?_, generating_function⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  exact linear k

end OpenMath.A024220

theorem OMA.solution : type_of% @OMA.S_oeis_a024220.main := by
  exact OpenMath.A024220.main
