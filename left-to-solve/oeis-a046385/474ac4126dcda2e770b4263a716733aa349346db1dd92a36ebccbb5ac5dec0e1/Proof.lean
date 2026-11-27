import OMAStatements.S_oeis_a046385

import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Tactic

private def residue (m a e : ℕ) : ℕ :=
  Nat.binaryRec' (motive := fun _ => ℕ) 1
    (fun b _ _ r => (r * r * (if b then a else 1)) % m) e

private theorem residue_cast (m a e : ℕ) :
    (residue m a e : ZMod m) = (a : ZMod m) ^ e := by
  induction e using Nat.binaryRec' with
  | zero => simp [residue]
  | bit b n hb ih =>
    unfold residue at *
    rw [Nat.binaryRec'_eq b n hb, ZMod.natCast_mod]
    have hb' : Nat.bit b n = n * 2 + b.toNat := by
      rw [Nat.bit_val, Nat.mul_comm 2 n]
    rw [hb', pow_add, pow_mul, pow_two]
    cases b
    · simp only [Bool.false_eq_true, if_false, mul_one, Nat.cast_mul]
      rw [ih]
      simp [Bool.toNat]
    · simp only [Nat.cast_mul]
      rw [ih]
      simp [Bool.toNat]

private theorem residue_one (m a e : ℕ) (h : residue m a e = 1) :
    (a : ZMod m) ^ e = 1 := by
  rw [← residue_cast, h, Nat.cast_one]

private theorem residue_not_one (m a e r : ℕ) (hm : 1 < m)
    (h : residue m a e = r) (hr : r < m) (hne : r ≠ 1) :
    (a : ZMod m) ^ e ≠ 1 := by
  intro he
  have hx : (r : ZMod m) = (1 : ℕ) := by rw [← h, residue_cast, he, Nat.cast_one]
  have hmod := (ZMod.natCast_eq_natCast_iff' r 1 m).mp hx
  rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hm] at hmod
  exact hne hmod

open OMA.S_oeis_a046385

private theorem prime_eq_of_dvd_power {p q e : ℕ} (hq : q.Prime) (hp : p.Prime)
    (h : q ∣ p ^ e) : q = p :=
  (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)

private theorem prime_2 : Nat.Prime 2 := by norm_num

private theorem prime_3 : Nat.Prime 3 := by norm_num

private theorem prime_5 : Nat.Prime 5 := by norm_num

private theorem prime_7 : Nat.Prime 7 := by norm_num

private theorem prime_11 : Nat.Prime 11 := by norm_num

private theorem prime_13 : Nat.Prime 13 := by norm_num

private theorem prime_17 : Nat.Prime 17 := by norm_num

private theorem prime_19 : Nat.Prime 19 := by norm_num

private theorem prime_29 : Nat.Prime 29 := by norm_num

private theorem prime_59 : Nat.Prime 59 := by norm_num

private theorem prime_97 : Nat.Prime 97 := by norm_num

private theorem prime_107 : Nat.Prime 107 := by norm_num

private theorem prime_181 : Nat.Prime 181 := by norm_num

private theorem prime_191 : Nat.Prime 191 := by norm_num

private theorem prime_383 : Nat.Prime 383 := by norm_num

private theorem prime_6959 : Nat.Prime 6959 := by norm_num

private theorem prime_9811 : Nat.Prime 9811 := by norm_num

private theorem prime_52579 : Nat.Prime 52579 := by norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_112691 : Nat.Prime 112691 := by
  apply lucas_primality 112691 2
  · exact residue_one _ _ _ (by decide)
  · intro q hq hdiv
    have hpred : (112691 : ℕ) - 1 = (2 ^ 1 : ℕ) * ((5 ^ 1 : ℕ) * ((59 ^ 1 : ℕ) * ((191 ^ 1 : ℕ)))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      exact residue_not_one _ _ _ 112690 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 5 := prime_eq_of_dvd_power hq prime_5 h1
      subst q
      exact residue_not_one _ _ _ 38357 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 59 := prime_eq_of_dvd_power hq prime_59 h2
      subst q
      exact residue_not_one _ _ _ 60899 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 191 := prime_eq_of_dvd_power hq prime_191 h3
      subst q
      exact residue_not_one _ _ _ 40527 (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_676147 : Nat.Prime 676147 := by
  apply lucas_primality 676147 14
  · exact residue_one _ _ _ (by decide)
  · intro q hq hdiv
    have hpred : (676147 : ℕ) - 1 = (2 ^ 1 : ℕ) * ((3 ^ 1 : ℕ) * ((112691 ^ 1 : ℕ))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      exact residue_not_one _ _ _ 676146 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 3 := prime_eq_of_dvd_power hq prime_3 h1
      subst q
      exact residue_not_one _ _ _ 272743 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 112691 := prime_eq_of_dvd_power hq prime_112691 h2
      subst q
      exact residue_not_one _ _ _ 91919 (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_5316677 : Nat.Prime 5316677 := by
  apply lucas_primality 5316677 2
  · exact residue_one _ _ _ (by decide)
  · intro q hq hdiv
    have hpred : (5316677 : ℕ) - 1 = (2 ^ 2 : ℕ) * ((191 ^ 1 : ℕ) * ((6959 ^ 1 : ℕ))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      exact residue_not_one _ _ _ 5316676 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 191 := prime_eq_of_dvd_power hq prime_191 h1
      subst q
      exact residue_not_one _ _ _ 5303307 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 6959 := prime_eq_of_dvd_power hq prime_6959 h2
      subst q
      exact residue_not_one _ _ _ 3037556 (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_315604633 : Nat.Prime 315604633 := by
  apply lucas_primality 315604633 5
  · exact residue_one _ _ _ (by decide)
  · intro q hq hdiv
    have hpred : (315604633 : ℕ) - 1 = (2 ^ 3 : ℕ) * ((3 ^ 1 : ℕ) * ((7 ^ 1 : ℕ) * ((97 ^ 1 : ℕ) * ((107 ^ 1 : ℕ) * ((181 ^ 1 : ℕ)))))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3 | h4 | h5
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      exact residue_not_one _ _ _ 315604632 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 3 := prime_eq_of_dvd_power hq prime_3 h1
      subst q
      exact residue_not_one _ _ _ 121169794 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 7 := prime_eq_of_dvd_power hq prime_7 h2
      subst q
      exact residue_not_one _ _ _ 220052836 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 97 := prime_eq_of_dvd_power hq prime_97 h3
      subst q
      exact residue_not_one _ _ _ 198114099 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 107 := prime_eq_of_dvd_power hq prime_107 h4
      subst q
      exact residue_not_one _ _ _ 263455579 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 181 := prime_eq_of_dvd_power hq prime_181 h5
      subst q
      exact residue_not_one _ _ _ 307515405 (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_66607329457 : Nat.Prime 66607329457 := by
  apply lucas_primality 66607329457 5
  · exact residue_one _ _ _ (by decide)
  · intro q hq hdiv
    have hpred : (66607329457 : ℕ) - 1 = (2 ^ 4 : ℕ) * ((3 ^ 3 : ℕ) * ((29 ^ 1 : ℕ) * ((5316677 ^ 1 : ℕ)))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      exact residue_not_one _ _ _ 66607329456 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 3 := prime_eq_of_dvd_power hq prime_3 h1
      subst q
      exact residue_not_one _ _ _ 4394086289 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 29 := prime_eq_of_dvd_power hq prime_29 h2
      subst q
      exact residue_not_one _ _ _ 55221327899 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 5316677 := prime_eq_of_dvd_power hq prime_5316677 h3
      subst q
      exact residue_not_one _ _ _ 37341785056 (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_1093122251956101862613 : Nat.Prime 1093122251956101862613 := by
  apply lucas_primality 1093122251956101862613 2
  · exact residue_one _ _ _ (by decide)
  · intro q hq hdiv
    have hpred : (1093122251956101862613 : ℕ) - 1 = (2 ^ 2 : ℕ) * ((13 ^ 1 : ℕ) * ((315604633 ^ 1 : ℕ) * ((66607329457 ^ 1 : ℕ)))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      exact residue_not_one _ _ _ 1093122251956101862612 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 13 := prime_eq_of_dvd_power hq prime_13 h1
      subst q
      exact residue_not_one _ _ _ 198297715337559890055 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 315604633 := prime_eq_of_dvd_power hq prime_315604633 h2
      subst q
      exact residue_not_one _ _ _ 280233819249029122975 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 66607329457 := prime_eq_of_dvd_power hq prime_66607329457 h3
      subst q
      exact residue_not_one _ _ _ 486406907673535899530 (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_58823529352941176529411764705882353 : Nat.Prime 58823529352941176529411764705882353 := by
  apply lucas_primality 58823529352941176529411764705882353 5
  · exact residue_one _ _ _ (by decide)
  · intro q hq hdiv
    have hpred : (58823529352941176529411764705882353 : ℕ) - 1 = (2 ^ 4 : ℕ) * ((3 ^ 1 : ℕ) * ((13 ^ 2 : ℕ) * ((9811 ^ 1 : ℕ) * ((676147 ^ 1 : ℕ) * ((1093122251956101862613 ^ 1 : ℕ)))))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3 | h4 | h5
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      exact residue_not_one _ _ _ 58823529352941176529411764705882352 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 3 := prime_eq_of_dvd_power hq prime_3 h1
      subst q
      exact residue_not_one _ _ _ 32672637095849678421468818515884796 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 13 := prime_eq_of_dvd_power hq prime_13 h2
      subst q
      exact residue_not_one _ _ _ 37292136811227784538995985997641137 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 9811 := prime_eq_of_dvd_power hq prime_9811 h3
      subst q
      exact residue_not_one _ _ _ 47141681791517524260994325838284074 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 676147 := prime_eq_of_dvd_power hq prime_676147 h4
      subst q
      exact residue_not_one _ _ _ 18341741981867400228704497655715717 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 1093122251956101862613 := prime_eq_of_dvd_power hq prime_1093122251956101862613 h5
      subst q
      exact residue_not_one _ _ _ 17428461981497196996246205369668996 (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_1000000000000000000000000001000000001000000001000000000000000000000000001 : Nat.Prime 1000000000000000000000000001000000001000000001000000000000000000000000001 := by
  apply lucas_primality 1000000000000000000000000001000000001000000001000000000000000000000000001 6
  · exact residue_one _ _ _ (by decide)
  · intro q hq hdiv
    have hpred : (1000000000000000000000000001000000001000000001000000000000000000000000001 : ℕ) - 1 = (2 ^ 27 : ℕ) * ((5 ^ 27 : ℕ) * ((7 ^ 1 : ℕ) * ((11 ^ 1 : ℕ) * ((13 ^ 1 : ℕ) * ((17 ^ 1 : ℕ) * ((19 ^ 1 : ℕ) * ((52579 ^ 1 : ℕ) * ((58823529352941176529411764705882353 ^ 1 : ℕ))))))))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      exact residue_not_one _ _ _ 1000000000000000000000000001000000001000000001000000000000000000000000000 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 5 := prime_eq_of_dvd_power hq prime_5 h1
      subst q
      exact residue_not_one _ _ _ 505957087895697068922855038886973661091283150978713499509537536600809527 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 7 := prime_eq_of_dvd_power hq prime_7 h2
      subst q
      exact residue_not_one _ _ _ 431520929471079023439547073250026922596032937718993242122618668352984556 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 11 := prime_eq_of_dvd_power hq prime_11 h3
      subst q
      exact residue_not_one _ _ _ 133401231133671072270323935187012898289944981758098452448208427543073450 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 13 := prime_eq_of_dvd_power hq prime_13 h4
      subst q
      exact residue_not_one _ _ _ 288086931430913887262447611770957757503437018220489417136106992038946234 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 17 := prime_eq_of_dvd_power hq prime_17 h5
      subst q
      exact residue_not_one _ _ _ 707348146015406768913978659141083473507205749731555616174922951115000447 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 19 := prime_eq_of_dvd_power hq prime_19 h6
      subst q
      exact residue_not_one _ _ _ 584566706908795806024907618016380610202278328520250520905704793850656833 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 52579 := prime_eq_of_dvd_power hq prime_52579 h7
      subst q
      exact residue_not_one _ _ _ 783833290445179115186877449215333001681387528756973675902831990002677582 (by decide) (by decide) (by decide) (by decide)
    · have he : q = 58823529352941176529411764705882353 := prime_eq_of_dvd_power hq prime_58823529352941176529411764705882353 h8
      subst q
      exact residue_not_one _ _ _ 265934078940434695053107819274394136538842382708616858943318810971177324 (by decide) (by decide) (by decide) (by decide)

private def factors : List ℕ := List.replicate 16 2 ++ List.replicate 3 3 ++ [383, 1000000000000000000000000001000000001000000001000000000000000000000000001]

private theorem listedPrime (p : ℕ) (hp : p ∈ factors) : p.Prime := by
  have h : p = 2 ∨ p = 3 ∨ p = 383 ∨ p = 1000000000000000000000000001000000001000000001000000000000000000000000001 := by
    simpa [factors, List.mem_replicate] using hp
  rcases h with rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_3
  · exact prime_383
  · exact prime_1000000000000000000000000001000000001000000001000000000000000000000000001

set_option maxRecDepth 10000 in
private theorem witness : 677707776000000000000000000677707776677707776677707776000000000000000000677707776 ∈ palindromesWithFactorCount 21 := by
  have hf : List.Perm factors (677707776000000000000000000677707776677707776677707776000000000000000000677707776 : ℕ).primeFactorsList :=
    Nat.primeFactorsList_unique (by decide) listedPrime
  refine ⟨by decide, by decide, hf.length_eq.symm.trans (by decide), ?_⟩
  intro p hp
  have h : p = 2 ∨ p = 3 ∨ p = 383 ∨ p = 1000000000000000000000000001000000001000000001000000000000000000000000001 := by
    simpa [factors, List.mem_replicate] using (hf.mem_iff.mpr hp)
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a046385.main) := by
  intro h
  classical
  have hex : ∃ n, n ∈ palindromesWithFactorCount 21 := ⟨677707776000000000000000000677707776677707776677707776000000000000000000677707776, witness⟩
  have hleast : IsLeast (palindromesWithFactorCount 21) (Nat.find hex) :=
    ⟨Nat.find_spec hex, fun _ hn => Nat.find_min' hex hn⟩
  have hbad := (h 21 (Nat.find hex)).mp hleast
  simp [knownTerms] at hbad
