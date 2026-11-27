import OMAStatements.S_oeis_a073409
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The congruence characterization of the greatest prime divisor in OEIS A073409. -/

namespace OpenMath.A073409

open Finset

open OMA.S_oeis_a073409 (a)

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

theorem main (n : ℕ) (hn : 0 < n) :
    IsGreatest {r : ℕ | r.Prime ∧ r ≤ 2*n+1 ∧
      ((r:ℤ)*(bernoulli (2*n)).num ≡ -((bernoulli (2*n)).den:ℤ) [ZMOD (r:ℤ)^2])} (a n) := by
  let B := bernoulli (2*n)
  let s := B.den.primeFactors
  have hnone : s.Nonempty := by
    have hmem : 2 ∈ correctionSet n := by
      simp [correctionSet, Nat.prime_two, hn]
    exact ⟨2, Nat.mem_primeFactors.mpr ⟨Nat.prime_two, (dvd_den_iff n 2 Nat.prime_two).mpr hmem, B.den_ne_zero⟩⟩
  have htop : a n = s.max' hnone := by
    unfold a
    rw [max'_eq_sup', sup'_eq_sup]
  have hmem : ∀ r : ℕ, r ∈ s ↔ r.Prime ∧ r ≤ 2*n+1 ∧
      ((r:ℤ)*B.num ≡ -(B.den:ℤ) [ZMOD (r:ℤ)^2]) := by
    intro r
    change r ∈ B.den.primeFactors ↔ _
    rw [Nat.mem_primeFactors_of_ne_zero B.den_ne_zero]
    constructor
    · rintro ⟨hp,hd⟩
      have hm : r ∈ correctionSet n := (dvd_den_iff n r hp).mp hd
      exact ⟨hp,by have := mem_range.mp (mem_filter.mp hm).1; omega,
        (congruence_iff_dvd n r hp).mpr hd⟩
    · rintro ⟨hp,_,hc⟩
      exact ⟨hp,(congruence_iff_dvd n r hp).mp hc⟩
  constructor
  · exact (hmem (a n)).mp (htop ▸ max'_mem _ _)
  · intro r hr
    have hm : r ∈ s := (hmem r).mpr hr
    rw [htop]
    exact le_max' _ _ hm

end OpenMath.A073409

theorem OMA.solution : type_of% @OMA.S_oeis_a073409.main := by
  exact OpenMath.A073409.main
