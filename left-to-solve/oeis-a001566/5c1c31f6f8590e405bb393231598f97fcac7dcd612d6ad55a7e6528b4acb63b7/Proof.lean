import OMAStatements.S_oeis_a001566
import Mathlib.Data.Nat.ModEq

/-!
# The squarefreeness conjecture in OEIS A001566

Gerald McGarvey's comment prints `8a+7`; its first four displayed values of `a`
agree with `40a+7`. Both readings have positive witnesses with square divisors.
Source: https://oeis.org/A001566/internal
-/

namespace OpenMath.A001566

def term : ℕ → ℕ
  | 0 => 3
  | n + 1 => term n ^ 2 - 2

/-- At this index the exact, positive quotient is divisible by a nontrivial square. -/
def Counterexample (scale n p : ℕ) : Prop :=
  7 < term n ∧ scale ∣ term n - 7 ∧ 1 < p ∧ p ^ 2 ∣ (term n - 7) / scale

theorem printed_counterexample : Counterexample 8 3 5 := by
  unfold Counterexample
  decide

theorem examples_counterexample : Counterexample 40 10 19 := by
  unfold Counterexample
  decide

/-- The squarefreeness clause fails on each reading, even among positive exact quotients. -/
theorem main : (∃ n p : ℕ, Counterexample 8 n p) ∧ (∃ n p : ℕ, Counterexample 40 n p) :=
  ⟨⟨3, 5, printed_counterexample⟩, ⟨10, 19, examples_counterexample⟩⟩

private theorem term_ge_three (n : ℕ) : 3 ≤ term n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hsquare : 3 * 3 ≤ term n ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul ih ih
    change 3 ≤ term n ^ 2 - 2
    omega

private theorem term_increasing : StrictMono term := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hsquare : 3 * term n ≤ term n ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right (term n) (term_ge_three n)
  have hn := term_ge_three n
  change term n < term n ^ 2 - 2
  omega

private theorem step_congr {m i j : ℕ} (h : term i ≡ term j [MOD m]) :
    term (i + 1) ≡ term (j + 1) [MOD m] := by
  have hi : 3 * 3 ≤ term i ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (term_ge_three i) (term_ge_three i)
  have hj : 3 * 3 ≤ term j ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (term_ge_three j) (term_ge_three j)
  change term i ^ 2 - 2 ≡ term j ^ 2 - 2 [MOD m]
  exact Nat.ModEq.sub (by omega) (by omega) (h.pow 2) (Nat.ModEq.refl 2)

private theorem repeat_residues (n : ℕ) : term (n + 10) ≡ term (n + 1) [MOD 14440] := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n.succ + 10 = n + 10 + 1 by omega]
    exact step_congr ih

private theorem repeated_seven (k : ℕ) : term (9 * k + 1) ≡ 7 [MOD 14440] := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 9 * k.succ + 1 = 9 * k + 10 by omega]
    exact (repeat_residues (9 * k)).trans ih

/-- Every later visit to residue seven in this cycle gives another counterexample. -/
theorem periodic_examples_counterexample (k : ℕ) : Counterexample 40 (9 * (k + 1) + 1) 19 := by
  have hpos : 7 < term (9 * (k + 1) + 1) := by
    change term 1 < term (9 * (k + 1) + 1)
    exact term_increasing (by omega)
  obtain ⟨q, hq⟩ := (repeated_seven (k + 1)).symm.dvd'
  have hfactor : term (9 * (k + 1) + 1) - 7 = (19 ^ 2 * q) * 40 := by omega
  have hquotient : (term (9 * (k + 1) + 1) - 7) / 40 = 19 ^ 2 * q := by
    rw [hfactor]
    simp
  exact ⟨hpos, ⟨19 ^ 2 * q, by rw [hfactor, Nat.mul_comm]⟩, by decide, ⟨q, hquotient⟩⟩

end OpenMath.A001566

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a001566.main) := by
  intro h
  have hd : (5 : ℕ) ^ 2 ∣ OMA.S_oeis_a001566.a 3 :=
    OpenMath.A001566.printed_counterexample.2.2.2
  exact h.1 3 (by decide) 5 (by decide) hd
