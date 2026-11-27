import OMAStatements.S_oeis_a234788
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The Bernoulli numerator residue claims in OEIS A234788. -/

namespace OpenMath.A234788

open Finset
open OMA.S_oeis_a234788 (commonResidues)

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

private abbrev correctionSet (n : ℕ) : Finset ℕ :=
  (range (2*n+2)).filter fun q => q.Prime ∧ (q-1) ∣ 2*n

private theorem correction_sum_integral (n r : ℕ) [Fact r.Prime] (s : Finset ℕ)
    (hs : s ⊆ correctionSet n) (hr : r ∉ s) :
    IntegralAt r (∑ q ∈ s, (1:ℚ)/(q:ℚ)) := by
  refine (Rat.padicValuation r).map_sum_le fun q hq => integral_one_div ?_
  have hp := (mem_filter.mp (hs hq)).2.1
  intro hd
  have he := (Nat.dvd_prime_two_le hp (Fact.out : r.Prime).two_le).mp hd
  exact hr (he ▸ hq)

private theorem integral_correction (n r : ℕ) [Fact r.Prime] (hr : r ∈ correctionSet n) :
    IntegralAt r (bernoulli (2*n) + (1:ℚ)/r) := by
  obtain ⟨z,hz⟩ := Bernoulli.vonStaudt_clausen n
  change (z:ℚ) = bernoulli (2*n) + ∑ q ∈ correctionSet n, (1:ℚ)/(q:ℚ) at hz
  rw [← sum_erase_add _ _ hr] at hz
  have hrep : bernoulli (2*n) + (1:ℚ)/r =
      (z:ℚ) - ∑ q ∈ (correctionSet n).erase r, (1:ℚ)/(q:ℚ) := by linarith
  rw [hrep]
  refine (Rat.padicValuation r).map_sub_le (Int.padicValuation_le_one r z) ?_
  exact correction_sum_integral n r _ (erase_subset _ _) (notMem_erase _ _)

private theorem dvd_den_iff (n r : ℕ) (hr : r.Prime) :
    r ∣ (bernoulli (2*n)).den ↔ r ∈ correctionSet n := by
  let : Fact r.Prime := ⟨hr⟩
  constructor
  · intro hD
    by_contra hnot
    obtain ⟨z,hz⟩ := Bernoulli.vonStaudt_clausen n
    have hrep : bernoulli (2*n) =
        (z:ℚ) - ∑ q ∈ correctionSet n, (1:ℚ)/(q:ℚ) := by
      change (z:ℚ) = bernoulli (2*n) + ∑ q ∈ correctionSet n, (1:ℚ)/(q:ℚ) at hz
      linarith
    have hd : IntegralAt r (bernoulli (2*n)) := by
      rw [hrep]
      exact (Rat.padicValuation r).map_sub_le (Int.padicValuation_le_one r z)
        (correction_sum_integral n r (correctionSet n) Subset.rfl hnot)
    exact (Rat.padicValuation_le_one_iff.mp hd) hD
  · intro hmem
    by_contra hnot
    have hi := integral_correction n r hmem
    have hb : IntegralAt r (bernoulli (2*n)) := Rat.padicValuation_le_one_iff.mpr hnot
    have hj := (Rat.padicValuation r).map_sub_le hi hb
    have hrat : bernoulli (2*n) + (1:ℚ)/r - bernoulli (2*n) = (1:ℚ)/r := by ring
    rw [hrat] at hj
    have hbad := Rat.padicValuation_le_one_iff.mp hj
    apply hbad
    simp [hr.ne_zero]

private theorem congruence_of_integral {B : ℚ} {r : ℕ} (hr : r.Prime)
    (hden : r ∣ B.den) (hcad : letI : Fact r.Prime := ⟨hr⟩; IntegralAt r (B+(1:ℚ)/r)) :
    (r:ℤ)*B.num ≡ -(B.den:ℤ) [ZMOD (r:ℤ)^2] := by
  let : Fact r.Prime := ⟨hr⟩
  let Y := B+(1:ℚ)/r
  have hY : IntegralAt r Y := hcad
  have hr0 : (r:ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hd0 : (B.den:ℚ) ≠ 0 := by exact_mod_cast B.den_ne_zero
  have hrat : Y = ((r:ℚ)*B.num+B.den)/((r:ℚ)*B.den) := by
    change B+(1:ℚ)/r = _
    conv_lhs => rw [← Rat.num_div_den B]
    field_simp
  have hscaled := (eq_div_iff (mul_ne_zero hr0 hd0)).mp hrat
  have hYden : Y*(Y.den:ℚ)=Y.num := by
    have hv : (Y.den:ℚ) ≠ 0 := by exact_mod_cast Y.den_ne_zero
    exact (eq_div_iff hv).mp (Rat.num_div_den Y).symm
  have heq : ((r:ℤ)*(B.den:ℤ))*Y.num = ((r:ℤ)*B.num+B.den)*(Y.den:ℤ) := by
    exact_mod_cast (show ((r:ℚ)*(B.den:ℚ))*(Y.num:ℚ) =
        ((r:ℚ)*(B.num:ℚ)+B.den)*(Y.den:ℚ) by
      rw [← hYden, ←hscaled]
      ring)
  have hdiv : (r:ℤ)^2 ∣ ((r:ℤ)*B.num+B.den)*(Y.den:ℤ) := by
    obtain ⟨k,hk⟩ := hden
    rw [← heq, hk]
    push_cast
    exact ⟨(k:ℤ)*Y.num, by ring⟩
  have hcop : (r^2).Coprime Y.den :=
    ((hr.coprime_iff_not_dvd).mpr (Rat.padicValuation_le_one_iff.mp hY)).pow_left 2
  have gcd1 : Int.gcd ((r:ℤ)^2) (Y.den:ℤ)=1 := by
    rw [← Nat.cast_pow, Int.gcd_natCast_natCast]
    exact hcop
  have hnum := Int.dvd_of_dvd_mul_left_of_gcd_one hdiv gcd1
  apply Int.modEq_iff_dvd.mpr
  rw [show -(B.den:ℤ)-(r:ℤ)*B.num = -((r:ℤ)*B.num+B.den) by ring, Int.dvd_neg]
  exact hnum

private theorem congruence_iff_dvd (n r : ℕ) (hr : r.Prime) :
    (r:ℤ)*(bernoulli (2*n)).num ≡ -((bernoulli (2*n)).den:ℤ) [ZMOD (r:ℤ)^2] ↔
      r ∣ (bernoulli (2*n)).den := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp h
    apply Int.natCast_dvd_natCast.mp
    use -((bernoulli (2*n)).num)-(r:ℤ)*k
    linear_combination -hk
  · intro hd
    let : Fact r.Prime := ⟨hr⟩
    exact congruence_of_integral hr hd (integral_correction n r ((dvd_den_iff n r hr).mp hd))

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

private theorem paired_reflect {R : Type*} [AddCommMonoid R] (f : ℕ → R) (h : ℕ) :
    (∑ i ∈ range (2*h+1), f i) = f 0 + ∑ i ∈ range h, (f (i+1) + f (2*h-i)) := by
  rw [show 2*h+1 = h+1+h by omega, sum_range_add, sum_range_succ']
  rw [← sum_range_reflect (fun i => f (h+1+i)) h]
  rw [sum_add_distrib]
  have heq : (∑ i ∈ range h, f (h+1+(h-1-i))) = ∑ i ∈ range h, f (2*h-i) := by
    refine sum_congr rfl fun i hi => congrArg f ?_
    have := mem_range.mp hi
    omega
  rw [heq]
  ac_rfl

private theorem paired_even_odd {R : Type*} [AddCommMonoid R] (f : ℕ → R) (h : ℕ) :
    (∑ i ∈ range (2*h+1), f i) = f 0 + ∑ i ∈ range h, (f (2*(i+1)) + f (2*h-2*i-1)) := by
  have ev : (∑ i ∈ range (2*h+1), f i) = f 0 + ∑ i ∈ range h, (f (2*(i+1)) + f (2*i+1)) := by
    induction h with
    | zero => simp
    | succ h ih =>
      rw [show 2*(h+1)+1 = (2*h+1)+1+1 by omega, sum_range_succ, sum_range_succ, ih, sum_range_succ]
      rw [show 2*h+1+1 = 2*(h+1) by omega]
      ac_rfl
  rw [ev, sum_add_distrib, sum_add_distrib]
  refine congrArg (f 0 + ·) (congrArg ((∑ i ∈ range h, f (2*(i+1))) + ·) ?_)
  rw [← sum_range_reflect (fun i => f (2*i+1)) h]
  refine sum_congr rfl fun i hi => congrArg f ?_
  have := mem_range.mp hi
  omega

private theorem pow_sqzero {R : Type*} [CommRing R] (x e : R) (he : e^2=0) (k : ℕ) :
    (x+e)^(k+1) = x^(k+1) + (k+1 : ℕ) * e * x^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ (x+e) (k+1), ih, pow_succ x (k+1), pow_succ x k]
    push_cast
    linear_combination ((k:R)+1) * x^k * he


private theorem reduced_faulhaber (r k : ℕ) [Fact r.Prime] (hr : 3 < r)
    (hk : 4 ≤ k) (he : Even k) (hcop : ¬r ∣ k+1) :
    ∃ T : ℚ, IntegralAt r T ∧
      (∑ i ∈ range r, (i:ℚ)^k) = (r:ℚ)*bernoulli k + (r:ℚ)^2*T := by
  let v (j : ℕ) : ℚ := bernoulli j * ((k+1).choose j) *
      (r:ℚ)^(k-1-j)/(k+1)
  refine ⟨∑ j ∈ range k, v j, ?_, ?_⟩
  · refine (Rat.padicValuation r).map_sum_le fun j hj => ?_
    have hjk := mem_range.mp hj
    by_cases hk1 : j = k-1
    · subst j
      have hodd : Odd (k-1) := by
        obtain ⟨i,hi⟩ := he
        exact ⟨i-1, by omega⟩
      simp [v, bernoulli_eq_zero_of_odd hodd (by omega)]
    · unfold v
      have heq : k-1-j = (k-2-j)+1 := by omega
      rw [heq, pow_succ]
      have h : bernoulli j * ((k+1).choose j) * ((r:ℚ)^(k-2-j)*(r:ℚ))/(k+1) =
          ((r:ℚ)*bernoulli j) *
          (((k+1).choose j:ℕ):ℚ) * (r:ℚ)^(k-2-j) * (1/(k+1:ℕ):ℚ) := by
        push_cast
        ring
      rw [h]
      refine integral_mul (integral_mul (integral_mul (integral_mul_bernoulli r j) ?_) ?_)
        (integral_one_div hcop)
      · exact Int.padicValuation_le_one r ((k+1).choose j)
      · exact_mod_cast Int.padicValuation_le_one r (r^(k-2-j):ℕ)
  · rw [sum_range_pow, sum_range_succ, Nat.choose_succ_self_right,
      show k+1-k = 1 by omega, pow_one]
    have hnz : (k:ℚ)+1 ≠ 0 := by positivity
    have hz : bernoulli k * ((k+1:ℕ):ℚ) * (r:ℚ)/(k+1) =
        (r:ℚ)*bernoulli k := by
      push_cast
      field_simp
    rw [hz, add_comm ((r:ℚ)*bernoulli k), mul_sum]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    have hjk := mem_range.mp hj
    unfold v
    rw [show k+1-j = (k-1-j)+2 by omega, pow_add]
    ring


private theorem reflect_pow {R : Type*} [CommRing R]
    (x e : R) (he : e^2=0) (m : ℕ) (hm : 0 < m) (hmEven : Even m) :
    (e-x)^m = x^m - (m:R)*e*x^(m-1) := by
  have hNeg : (e-x)^m = (x-e)^m := by
    rw [show e-x=-(x-e) by ring]
    exact hmEven.neg_pow _
  rw [hNeg, sub_eq_add_neg]
  obtain ⟨k,rfl⟩ : ∃ k, m = k+1 := ⟨m-1, by omega⟩
  rw [pow_sqzero x (-e) (by simpa using he) k, Nat.add_sub_cancel]
  ring

private theorem reflected_sum {R : Type*} [CommRing R] (r h m : ℕ) (g : ℕ → ℕ)
    (hr : (r:R)^2=0) (hm : 0 < m) (he : Even m)
    (hg : ∀ i ∈ range h, g i ≤ r) :
    (∑ i ∈ range h, ((g i:R)^m + ((r-g i:ℕ):R)^m)) =
      2*(∑ i ∈ range h, (g i:R)^m) -
        (m:R)*(r:R)*(∑ i ∈ range h, (g i:R)^(m-1)) := by
  have hs : ∀ i ∈ range h, ((r-g i:ℕ):R)^m =
      (g i:R)^m - (m:R)*(r:R)*(g i:R)^(m-1) := by
    intro i hi
    rw [Nat.cast_sub (hg i hi)]
    exact reflect_pow (g i:R) (r:R) hr m hm he
  calc
    _ = ∑ i ∈ range h, ((g i:R)^m + (g i:R)^m -
          (m:R)*(r:R)*(g i:R)^(m-1)) := by
      apply sum_congr rfl
      intro i hi
      rw [hs i hi]
      ring
    _ = _ := by
      rw [sum_sub_distrib, sum_add_distrib, ←mul_sum]
      ring

private theorem paired_power_sums {R : Type*} [CommRing R] (r h m : ℕ)
    (hrh : r = 2*h+1) (hr : (r:R)^2=0) (hm : 0 < m) (he : Even m) :
    ((2:R)^m-1)*(∑ i ∈ range r, (i:R)^m) =
      -(m:R)*(r:R)*(2:R)^(m-1)*(∑ i ∈ range h, ((i+1:ℕ):R)^(m-1)) := by
  let S : R := ∑ i ∈ range r, (i:R)^m
  let H : R := ∑ i ∈ range h, ((i+1:ℕ):R)^(m-1)
  let U : R := ∑ i ∈ range h, ((i+1:ℕ):R)^m
  have h1 : S = 2*U-(m:R)*(r:R)*H := by
    unfold S
    conv_lhs => rw [hrh, paired_reflect (fun i => (i:R)^m), Nat.cast_zero, zero_pow hm.ne', zero_add]
    have hF := reflected_sum (R:=R) r h m (fun i => i+1) hr hm he
      (fun i hi => by have := mem_range.mp hi; omega)
    refine (sum_congr rfl fun i hi => ?_).trans hF
    have := mem_range.mp hi
    rw [show 2*h-i = r-(i+1) by omega]
  have h2 : S = 2*(2:R)^m*U-(m:R)*(r:R)*(2:R)^(m-1)*H := by
    unfold S
    conv_lhs => rw [hrh, paired_even_odd (fun i => (i:R)^m), Nat.cast_zero, zero_pow hm.ne', zero_add]
    have hF := reflected_sum (R:=R) r h m (fun i => 2*(i+1)) hr hm he
      (fun i hi => by have := mem_range.mp hi; omega)
    calc
      _ = ∑ i ∈ range h, (((2*(i+1):ℕ):R)^m + ((r-2*(i+1):ℕ):R)^m) := by
        refine sum_congr rfl fun i hi => ?_
        have := mem_range.mp hi
        rw [show 2*h-2*i-1 = r-2*(i+1) by omega]
      _ = _ := by
        rw [hF]
        simp_rw [Nat.cast_mul, Nat.cast_ofNat, mul_pow, ←mul_sum]
        change 2*((2:R)^m*U)-(m:R)*(r:R)*((2:R)^(m-1)*H) = _
        ring
  change ((2:R)^m-1)*S = -(m:R)*(r:R)*(2:R)^(m-1)*H
  have hA : (2:R)^m = 2*(2:R)^(m-1) := by
    rw [show m = (m-1)+1 by omega, pow_succ]
    simp [mul_comm]
  linear_combination (2:R)^m*h1-h2-(m:R)*(r:R)*H*hA


private theorem pow_mod_period {r d t : ℕ} [Fact r.Prime] (hd : d ≠ 0) (x : ZMod r) :
    x^(d+(r-1)*t)=x^d := by
  by_cases hx : x = 0
  · subst x
    have hh : d+(r-1)*t ≠ 0 := by omega
    simp [zero_pow hd, zero_pow hh]
  · rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, mul_one]

private theorem power_sum_residue (r m : ℕ) [Fact r.Prime] (hr : 3 < r)
    (hm : 4 ≤ m) (he : Even m) (hd : r-1 ∣ m-2) :
    ∃ T : ℤ, (∑ i ∈ range r, (i:ℤ)^m) = (r:ℤ)*T ∧
      12*T ≡ (m:ℤ) [ZMOD r] := by
  let S : ℤ := ∑ i ∈ range r, (i:ℤ)^m
  let h := (r-1)/2
  let H : ℤ := ∑ i ∈ range h, ((i+1:ℕ):ℤ)^(m-1)
  have hrh : r = 2*h+1 := by
    obtain ⟨a,ha⟩ := (Fact.out : r.Prime).odd_of_ne_two (by omega)
    omega
  obtain ⟨t,ht⟩ := hd
  have power_m (x : ZMod r) : x^m=x^2 := by
    rw [show m=2+(r-1)*t by omega]
    exact pow_mod_period (by decide) x
  have power_pred (x : ZMod r) : x^(m-1)=x := by
    rw [show m-1=1+(r-1)*t by omega]
    simpa using pow_mod_period (d:=1) (t:=t) (by decide) x
  have h3 : (3:ZMod r) ≠ 0 := by
    exact_mod_cast (mt (ZMod.natCast_eq_zero_iff 3 r).mp
      (Nat.not_dvd_of_pos_of_lt (by decide : 0<3) hr))
  have hs : (S:ZMod r) = 0 := by
    have hh := paired_power_sums (R:=ZMod r) r h m hrh (by simp) (by omega) he
    rw [power_m] at hh
    have hs0 : (3:ZMod r)*(S:ZMod r) = 0 := by
      norm_num [ZMod.natCast_self] at hh
      simpa [S] using hh
    exact (mul_eq_zero.mp hs0).resolve_left h3
  obtain ⟨T,hT⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd S r).mp hs
  refine ⟨T,hT,?_⟩

  have hR : ((r:ZMod (r^2))^2) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have h2 := paired_power_sums (R:=ZMod (r^2)) r h m hrh hR (by omega) he
  have hmod : ((2:ℤ)^m-1)*S ≡ -(m:ℤ)*(r:ℤ)*(2:ℤ)^(m-1)*H [ZMOD (r:ℤ)^2] := by
    rw [← Nat.cast_pow, ← ZMod.intCast_eq_intCast_iff]
    push_cast [S, H]
    simpa only [Nat.cast_succ] using h2
  rw [hT] at hmod
  have hcanc : (r:ℤ)*(((2:ℤ)^m-1)*T) ≡
      (r:ℤ)*(-(m:ℤ)*(2:ℤ)^(m-1)*H) [ZMOD (r:ℤ)*(r:ℤ)] := by
    simpa only [pow_two (r:ℤ), mul_left_comm, mul_assoc, mul_comm] using hmod
  have hlast := hcanc.mul_left_cancel' (show (r:ℤ) ≠ 0 by omega)
  rw [← ZMod.intCast_eq_intCast_iff] at hlast
  push_cast at hlast
  rw [power_m, power_pred] at hlast
  have hfactor :
      8*(H:ZMod r) = -1 := by
    have hnat : (∑ i ∈ range h, (i+1))*2 = (h+1)*h := by
      simpa only [sum_range_succ', add_zero, zero_add, Nat.add_sub_cancel] using sum_range_id_mul_two (h+1)
    have hz := congrArg (fun n:ℕ => (n:ZMod r)) hnat
    push_cast at hz
    have hsqr : (2*(h:ZMod r)+1)^2=0 := by
      have heq := congrArg (fun n:ℕ => (n:ZMod r)) hrh
      push_cast at heq
      rw [← heq]
      simp
    have hH : (H:ZMod r) = ∑ i ∈ range h, ((i+1:ℕ):ZMod r) := by
      unfold H
      rw [Int.cast_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [Int.cast_pow, Int.cast_natCast, power_pred]
    rw [hH]
    simp only [Nat.cast_succ]
    linear_combination 4*hz + hsqr
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  linear_combination 4*hlast - (m:ZMod r)*hfactor


private theorem correction_prod_eq_den (n : ℕ) :
    ∏ p ∈ correctionSet n, p = (bernoulli (2*n)).den := by
  let B := bernoulli (2*n)
  have hs : Squarefree B.den := Nat.squarefree_iff_prime_squarefree.mpr (by
    intro r hr hdiv
    let : Fact r.Prime := ⟨hr⟩
    have hi : IntegralAt r ((r:ℚ)*B) := integral_mul_bernoulli r (2*n)
    have hnot := Rat.padicValuation_le_one_iff.mp hi
    have hr0 : (r:ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
    have hv : B = ((1:ℚ)/r)*((r:ℚ)*B) := by field_simp
    have hfac := Rat.mul_den_dvd ((1:ℚ)/r) ((r:ℚ)*B)
    rw [←hv] at hfac
    have hd : ((1:ℚ)/r).den = r := by simp [hr.ne_zero]
    rw [hd] at hfac
    exact hnot (Nat.dvd_of_mul_dvd_mul_left hr.pos (hdiv.trans hfac)))
  have hset : correctionSet n = B.den.primeFactors := by
    ext p
    constructor
    · intro hp
      have hpr := (mem_filter.mp hp).2.1
      exact Nat.mem_primeFactors.mpr ⟨hpr,(dvd_den_iff n p hpr).mpr hp,B.den_ne_zero⟩
    · intro hp
      obtain ⟨hr,hd,_⟩ := Nat.mem_primeFactors.mp hp
      exact (dvd_den_iff n p hr).mp hd
  rw [hset, Nat.prod_primeFactors_of_squarefree hs]

private theorem six_dvd_den (n : ℕ) (hn : 0 < n) : 6 ∣ (bernoulli (2*n)).den := by
  have h2 : 2 ∣ (bernoulli (2*n)).den :=
    (dvd_den_iff n 2 Nat.prime_two).mpr (by simp [correctionSet, Nat.prime_two, hn])
  have h3 : 3 ∣ (bernoulli (2*n)).den :=
    (dvd_den_iff n 3 Nat.prime_three).mpr
      (mem_filter.mpr ⟨mem_range.mpr (by omega), Nat.prime_three, by simp⟩)
  exact (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3

private theorem num_mod_six (n : ℕ) (hn : 0 < n) :
    (bernoulli (2*n)).num ≡ (((bernoulli (2*n)).den / 6 :ℕ):ℤ) [ZMOD 6] := by
  let B := bernoulli (2*n)
  have hD := six_dvd_den n hn
  have h2 : (2:ℕ) ∣ B.den := (show 2 ∣ (6:ℕ) by decide).trans hD
  have h3 : (3:ℕ) ∣ B.den := (show 3 ∣ (6:ℕ) by decide).trans hD
  have h2c := Int.modEq_iff_dvd.mp ((congruence_iff_dvd n 2 Nat.prime_two).mpr h2)
  have h3c := Int.modEq_iff_dvd.mp ((congruence_iff_dvd n 3 Nat.prime_three).mpr h3)
  obtain ⟨x,hx⟩ := h2c
  obtain ⟨y,hy⟩ := h3c
  obtain ⟨z,hz⟩ := hD
  have hz' : B.den / 6 = z := by rw [hz, Nat.mul_div_cancel_left _ (by decide : 0 < 6)]
  have hzI : (B.den:ℤ) = 6*(z:ℤ) := by exact_mod_cast hz
  change -(B.den:ℤ)-2*B.num = (2:ℤ)^2*x at hx
  change -(B.den:ℤ)-3*B.num = (3:ℤ)^2*y at hy
  rw [hzI] at hx hy
  norm_num at hx hy
  change B.num ≡ ((B.den/6:ℕ):ℤ) [ZMOD 6]
  apply Int.modEq_iff_dvd.mpr
  rw [hz']
  exact ⟨(z:ℤ)+x-y, by omega⟩

private theorem int_zero_of_scale {r : ℕ} [Fact r.Prime] (X : ℤ) (Y : ℚ)
    (hY : IntegralAt r Y) (heq : (X:ℚ) = (r:ℚ)*Y) :
    (X:ZMod r) = 0 := by
  have hd : ¬r∣Y.den := Rat.padicValuation_le_one_iff.mp hY
  have hd0 : (Y.den:ℚ) ≠ 0 := by exact_mod_cast Y.den_ne_zero
  have hYD : Y*(Y.den:ℚ)=Y.num := (eq_div_iff hd0).mp (Rat.num_div_den Y).symm
  have hI : X*(Y.den:ℤ)=(r:ℤ)*Y.num := by
    exact_mod_cast (show (X:ℚ)*(Y.den:ℚ)=(r:ℚ)*(Y.num:ℚ) by
      rw [heq,mul_assoc,hYD])
  have hR := congrArg (fun x : ℤ => (x:ZMod r)) hI
  push_cast at hR
  have hn : (Y.den:ZMod r) ≠ 0 := mt (ZMod.natCast_eq_zero_iff Y.den r).mp hd
  have hR' : (X:ZMod r)*(Y.den:ZMod r)=0 := by simpa using hR
  exact (mul_eq_zero.mp hR').resolve_right hn

private theorem mod_five_degree (k : ℕ) :
    (bernoulli (20*k+2)).num ≡ (((bernoulli (20*k+2)).den / 6 :ℕ):ℤ) [ZMOD 5] := by
  let m := 20*k+2
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  by_cases hk0 : k=0
  · subst k
    norm_num [bernoulli_two]
  have hm4 : 4 ≤ m := by omega
  have hmE : Even m := ⟨10*k+1, by omega⟩
  obtain ⟨T,hT,hmod⟩ := power_sum_residue 5 m (by decide) hm4 hmE ⟨5*k, by omega⟩
  obtain ⟨U,hU,hf⟩ := reduced_faulhaber 5 m (by decide) hm4 hmE (by omega)
  let B := bernoulli m
  have hTR : (∑ i ∈ range 5, (i:ℚ)^m) = (5:ℚ)*(T:ℚ) := by exact_mod_cast hT
  have hBR : (B:ℚ) = (B.num:ℚ)/(B.den:ℚ) := (Rat.num_div_den B).symm
  have hd0 : (B.den:ℚ) ≠ 0 := by exact_mod_cast B.den_ne_zero
  have hdenR : B*(B.den:ℚ) = B.num := (eq_div_iff hd0).mp hBR
  change (∑ i ∈ range 5, (i:ℚ)^m) = 5*B+5^2*U at hf
  rw [hTR] at hf
  have Ucalc : (T:ℚ)= B+5*U := by linarith
  have hEq : (((B.den:ℤ)*T-B.num:ℤ):ℚ) = (5:ℚ)*((B.den:ℚ)*U) := by
    push_cast
    linear_combination (B.den:ℚ)*Ucalc + hdenR
  have hIn : IntegralAt 5 ((B.den:ℚ)*U) :=
    integral_mul (Int.padicValuation_le_one 5 B.den) hU
  have hForm := int_zero_of_scale (r:=5) ((B.den:ℤ)*T-B.num) ((B.den:ℚ)*U) hIn hEq
  have hN : (B.den:ℤ)*T ≡ B.num [ZMOD ((5:ℕ):ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ 5).mp
    rw [Int.cast_sub] at hForm
    exact sub_eq_zero.mp hForm
  have hmod' := hmod.mul_left (B.den:ℤ)
  have hNeq : 12*B.num ≡ (m:ℤ)*(B.den:ℤ) [ZMOD ((5:ℕ):ℤ)] :=
    (hN.mul_left 12).symm.trans (by simpa only [mul_comm,mul_left_comm,mul_assoc] using hmod')
  have hM : (m:ℤ) ≡ 2 [ZMOD ((5:ℕ):ℤ)] := by
    refine Int.modEq_iff_dvd.mpr ⟨-4*(k:ℤ),?_⟩
    simp only [m, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hzD : 6 ∣ B.den := by
    have hD := six_dvd_den (10*k+1) (by omega)
    simpa only [show 2*(10*k+1) = m by omega] using hD
  obtain ⟨z,hz⟩ := hzD
  have hz' : B.den/6 = z := by rw [hz, Nat.mul_div_cancel_left _ (by decide : 0 < 6)]
  have hzI : (B.den:ℤ) = 6*(z:ℤ) := by exact_mod_cast hz
  have hFull := hNeq.trans (hM.mul_right (B.den:ℤ))
  rw [hzI, ← mul_assoc, show (2:ℤ)*6 = 12 by decide] at hFull
  have hmul : (5:ℤ) ∣ ((z:ℤ)-B.num)*12 := by
    rw [show ((z:ℤ)-B.num)*12 = 12*z-12*B.num by ring]
    exact Int.modEq_iff_dvd.mp hFull
  change B.num ≡ ((B.den/6:ℕ):ℤ) [ZMOD 5]
  rw [hz']
  exact Int.modEq_iff_dvd.mpr (Int.dvd_of_dvd_mul_left_of_gcd_one hmul (by decide))

private theorem mod_thirty_degree (k : ℕ) :
    (bernoulli (20*k+2)).num ≡ (((bernoulli (20*k+2)).den / 6 :ℕ):ℤ) [ZMOD 30] := by
  have h5 := Int.modEq_iff_dvd.mp (mod_five_degree k)
  have h6 := Int.modEq_iff_dvd.mp (num_mod_six (10*k+1) (by omega))
  rw [show 2*(10*k+1)=20*k+2 by omega] at h6
  obtain ⟨s,hs⟩ := h5
  obtain ⟨t,ht⟩ := h6
  exact Int.modEq_iff_dvd.mpr ⟨s-t, by omega⟩


private theorem common_are_units {r : ℕ} (hr : r ∈ commonResidues) :
    r ∈ ({1,7,11,13,17,19,23,29} : Set ℕ) := by
  obtain ⟨n,hn,hcon,hres⟩ := hr
  let B := bernoulli (2*n)
  let T := B.den/6
  change r = T%30 at hres
  have hTD : 6*T = B.den := Nat.mul_div_cancel' (six_dvd_den n hn)
  have hconD : (30:ℤ) ∣ (T:ℤ)-B.num := Int.modEq_iff_dvd.mp hcon
  have hnot : ∀ p : ℕ, p.Prime → p ∣ 30 → ¬p∣r := by
    intro p hp hp30 hd
    have hrt : T = 30*(T/30)+r := by omega
    have hpT : p ∣ T := by
      rw [hrt]
      exact Nat.dvd_add (dvd_mul_of_dvd_left hp30 _) hd
    have hPD : p ∣ B.den := hTD ▸ dvd_mul_of_dvd_right hpT 6
    have hPdiff : (p:ℤ)∣(T:ℤ)-B.num := (Int.natCast_dvd_natCast.mpr hp30).trans hconD
    have hnum : (p:ℤ)∣B.num := by
      have h := Int.dvd_sub (Int.natCast_dvd_natCast.mpr hpT) hPdiff
      rwa [sub_sub_cancel] at h
    have hG : p ∣ Nat.gcd B.num.natAbs B.den := Nat.dvd_gcd (Int.natCast_dvd.mp hnum) hPD
    have hReduced : Nat.gcd B.num.natAbs B.den = 1 := B.reduced
    rw [hReduced] at hG
    exact hp.ne_one (Nat.dvd_one.mp hG)
  have hC : Nat.Coprime r 30 := by
    by_contra hBad
    obtain ⟨p,hp,hg⟩ := Nat.exists_prime_and_dvd (n:=Nat.gcd r 30) hBad
    exact hnot p hp (hg.trans (Nat.gcd_dvd_right _ _)) (hg.trans (Nat.gcd_dvd_left _ _))
  have hlt : r < 30 := by rw [hres]; exact Nat.mod_lt _ (by decide)
  have hFinite : ∀ t : Fin 30, t.val.Coprime 30 →
      t.val ∈ ({1,7,11,13,17,19,23,29} : Finset ℕ) := by decide +kernel
  simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] using hFinite ⟨r,hlt⟩ hC


private def witnessCorrection (n : ℕ) : Finset ℕ :=
  (((2*n).divisors).image (fun d => d+1)).filter Nat.Prime

private theorem witness_correction_eq (n : ℕ) (hn : 0 < n) :
    witnessCorrection n = correctionSet n := by
  ext q
  constructor
  · intro h
    obtain ⟨hq,hpr⟩ := mem_filter.mp h
    obtain ⟨d,hd,he⟩ := mem_image.mp hq
    obtain ⟨hdv,_⟩ := Nat.mem_divisors.mp hd
    have hle := Nat.le_of_dvd (by omega : 0 < 2*n) hdv
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),hpr,by convert hdv using 1; omega⟩
  · intro h
    obtain ⟨_,hpr,hdv⟩ := mem_filter.mp h
    have hq := hpr.two_le
    exact mem_filter.mpr ⟨mem_image.mpr ⟨q-1,Nat.mem_divisors.mpr ⟨hdv,by omega⟩,by omega⟩,hpr⟩

private theorem witness (k r : ℕ)
    (hr : ((∏ p ∈ witnessCorrection (10*k+1), p)/6)%30 = r) : r ∈ commonResidues := by
  refine ⟨10*k+1, by omega, ?_, ?_⟩
  · simpa only [show 2*(10*k+1)=20*k+2 by omega] using mod_thirty_degree k
  · rw [← correction_prod_eq_den, ← witness_correction_eq _ (by omega)]
    exact hr.symm

theorem main :
    (∀ k : ℕ, (bernoulli (20*k+2)).num ≡ (((bernoulli (20*k+2)).den/6 :ℕ):ℤ) [ZMOD 30]) ∧
    commonResidues = ({1,7,11,13,17,19,23,29} : Set ℕ) := by
  refine ⟨mod_thirty_degree,?_⟩
  ext r
  refine ⟨common_are_units,?_⟩
  intro h
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness 0 1 (by decide +kernel)
  · exact witness 20 7 (by decide +kernel)
  · exact witness 26 11 (by decide +kernel)
  · exact witness 17 13 (by decide +kernel)
  · exact witness 16 17 (by decide +kernel)
  · exact witness 8 19 (by decide +kernel)
  · exact witness 1 23 (by decide +kernel)
  · exact witness 62 29 (by decide +kernel)

end OpenMath.A234788

theorem OMA.solution : type_of% @OMA.S_oeis_a234788.main := by
  exact OpenMath.A234788.main
