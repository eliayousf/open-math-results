import OMAStatements.S_oeis_a363151
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The Bernoulli convolutions in OEIS A363151 have cubefree denominators. -/

namespace OpenMath.A363151

open Finset

open OMA.S_oeis_a363151 (a)

private abbrev IntegralAt (r : ℕ) [Fact r.Prime] (x : ℚ) : Prop :=
  Rat.padicValuation r x ≤ 1

private theorem integral_mul {r : ℕ} [Fact r.Prime] {x y : ℚ}
    (hx : IntegralAt r x) (hy : IntegralAt r y) : IntegralAt r (x*y) :=
  ((Rat.padicValuation r).map_mul x y).trans_le (mul_le_one' hx hy)

private theorem integral_one_div {r s : ℕ} [Fact r.Prime]
    (hrs : ¬ r ∣ s) : IntegralAt r (1 / (s:ℚ)) := by
  apply Rat.padicValuation_le_one_iff.mpr
  intro hd
  apply hrs
  refine hd.trans ?_
  rw [show (1:ℚ) / (s:ℚ) = Rat.divInt 1 s by rw [Rat.divInt_eq_div]; norm_num]
  exact Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _)

private theorem integral_mul_bernoulli (r j : ℕ) [Fact r.Prime] : IntegralAt r ((r:ℚ) * bernoulli j) := by
  obtain he | ho := Nat.even_or_odd j
  · obtain ⟨k,hk⟩ := he
    rw [show j = 2*k by omega]
    obtain ⟨z,hz⟩ := Bernoulli.vonStaudt_clausen k
    have hv := congrArg (fun x : ℚ => (r:ℚ) * x) hz
    rw [mul_add, mul_sum] at hv
    rw [show (r:ℚ) * bernoulli (2*k) = (r:ℚ)*z -
      ∑ s ∈ range (2*k+2) with s.Prime ∧ (s-1) ∣ 2*k, (r:ℚ) * (1/(s:ℚ)) by linarith]
    refine (Rat.padicValuation r).map_sub_le ?_ ?_
    · exact integral_mul (Int.padicValuation_le_one r r) (Int.padicValuation_le_one r z)
    · refine (Rat.padicValuation r).map_sum_le fun s hs => ?_
      by_cases hrs : s = r
      · subst s
        have hr0 : (r:ℚ) ≠ 0 := by exact_mod_cast (Fact.out : r.Prime).ne_zero
        rw [← mul_div_assoc, mul_one, div_self hr0]
        simp
      · refine integral_mul (Int.padicValuation_le_one r r) (integral_one_div ?_)
        have hsp : s.Prime := (mem_filter.mp hs).2.1
        intro h
        exact hrs ((Nat.dvd_prime_two_le hsp (Fact.out : r.Prime).two_le).mp h).symm
  · by_cases hj : j = 1
    · subst j
      by_cases hr2 : r = 2
      · subst r
        norm_num [bernoulli_one, IntegralAt]
      rw [bernoulli_one]
      have hprime := (Fact.out : r.Prime).two_le
      have h2 : ¬r∣2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
      have hh := integral_mul (Int.padicValuation_le_one r r) (integral_one_div h2)
      rw [show (r:ℚ) * (-1/2) = -((r:ℚ)*(1/2)) by ring]
      change Rat.padicValuation r (-((r:ℚ)*(1/2))) ≤ 1
      rw [Valuation.map_neg]
      exact hh
    · rw [bernoulli_eq_zero_of_odd ho (by obtain ⟨i,hi⟩ := ho; omega), mul_zero]
      simp

private theorem integral_mul_bernoulli' (r j : ℕ) [Fact r.Prime] :
    IntegralAt r ((r : ℚ) * bernoulli' j) := by
  rw [bernoulli'_eq_bernoulli, ← mul_assoc, mul_comm (r : ℚ), mul_assoc]
  refine integral_mul ?_ (integral_mul_bernoulli r j)
  exact_mod_cast Int.padicValuation_le_one r ((-1 : ℤ) ^ j)

private theorem denominator_dvd_scale {x : ℚ} {r : ℕ} (hr0 : r ≠ 0) :
    x.den ∣ r ^ 2 * (((r : ℚ) ^ 2 * x).den) := by
  have h : x = (1 / ((r ^ 2 : ℕ) : ℚ)) * ((r : ℚ) ^ 2 * x) := by
    push_cast
    have hr0' : (r : ℚ) ≠ 0 := by exact_mod_cast hr0
    field_simp
  have hfrac : (1 / ((r ^ 2 : ℕ) : ℚ)).den ∣ r ^ 2 := by
    rw [show (1 : ℚ) / ((r ^ 2 : ℕ) : ℚ) = Rat.divInt 1 (r ^ 2 : ℕ) by
      rw [Rat.divInt_eq_div]; norm_num]
    exact Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _)
  let y := (r : ℚ) ^ 2 * x
  have hd := Rat.mul_den_dvd (1 / ((r ^ 2 : ℕ) : ℚ)) y
  have hxy : x = (1 / ((r ^ 2 : ℕ) : ℚ)) * y := h
  rw [← hxy] at hd
  exact hd.trans (Nat.mul_dvd_mul_right hfrac _)

theorem main (n r : ℕ) (hr : Nat.Prime r) : ¬ r ^ 3 ∣ a n := by
  let : Fact r.Prime := ⟨hr⟩
  let x : ℚ := ∑ j ∈ range (n + 1), bernoulli' j * bernoulli' (n-j)
  have hIntegral : IntegralAt r ((r : ℚ) ^ 2 * x) := by
    unfold x
    rw [mul_sum]
    refine (Rat.padicValuation r).map_sum_le fun j _ => ?_
    rw [show (r : ℚ) ^ 2 * (bernoulli' j * bernoulli' (n-j)) =
        ((r : ℚ) * bernoulli' j) * ((r : ℚ) * bernoulli' (n-j)) by ring]
    exact integral_mul (integral_mul_bernoulli' r j) (integral_mul_bernoulli' r (n-j))
  have hNot := Rat.padicValuation_le_one_iff.mp hIntegral
  intro h
  unfold a at h
  simp only [Polynomial.bernoulli_eval_one] at h
  change r ^ 3 ∣ x.den at h
  have hdiv := h.trans (denominator_dvd_scale hr.ne_zero)
  rw [show r ^ 3 = r ^ 2 * r by rfl] at hdiv
  exact hNot (Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos hr.pos) hdiv)

end OpenMath.A363151

theorem OMA.solution : type_of% @OMA.S_oeis_a363151.main := by
  exact OpenMath.A363151.main
