import OMAStatements.S_mo_254323
import Mathlib.NumberTheory.ArithmeticFunction.Misc

import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

private theorem prime_eq_of_dvd_power {p q e : ℕ} (hq : q.Prime) (hp : p.Prime)
    (h : q ∣ p ^ e) : q = p :=
  (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)

private theorem prime_2 : Nat.Prime 2 := by norm_num

private theorem prime_3 : Nat.Prime 3 := by norm_num

private theorem prime_5 : Nat.Prime 5 := by norm_num

private theorem prime_11 : Nat.Prime 11 := by norm_num

private theorem prime_13 : Nat.Prime 13 := by norm_num

private theorem prime_17 : Nat.Prime 17 := by norm_num

private theorem prime_19 : Nat.Prime 19 := by norm_num

private theorem prime_23 : Nat.Prime 23 := by norm_num

private theorem prime_29 : Nat.Prime 29 := by norm_num

private theorem prime_31 : Nat.Prime 31 := by norm_num

private theorem prime_37 : Nat.Prime 37 := by norm_num

private theorem prime_47 : Nat.Prime 47 := by norm_num

private theorem prime_53 : Nat.Prime 53 := by norm_num

private theorem prime_89 : Nat.Prime 89 := by norm_num

private theorem prime_97 : Nat.Prime 97 := by norm_num

private theorem prime_101 : Nat.Prime 101 := by norm_num

private theorem prime_127 : Nat.Prime 127 := by norm_num

private theorem prime_229 : Nat.Prime 229 := by norm_num

private theorem prime_239 : Nat.Prime 239 := by norm_num

private theorem prime_251 : Nat.Prime 251 := by norm_num

private theorem prime_293 : Nat.Prime 293 := by norm_num

private theorem prime_307 : Nat.Prime 307 := by norm_num

private theorem prime_463 : Nat.Prime 463 := by norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_1451 : Nat.Prime 1451 := by
  apply lucas_primality 1451 2
  · change (2 : ZMod 1451) ^ 1450 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (1451 : ℕ) - 1 = (2 ^ 1 : ℕ) * ((5 ^ 2 : ℕ) * ((29 ^ 1 : ℕ))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (2 : ZMod 1451) ^ 725 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 5 := prime_eq_of_dvd_power hq prime_5 h1
      subst q
      change (2 : ZMod 1451) ^ 290 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 29 := prime_eq_of_dvd_power hq prime_29 h2
      subst q
      change (2 : ZMod 1451) ^ 50 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_1861 : Nat.Prime 1861 := by
  apply lucas_primality 1861 2
  · change (2 : ZMod 1861) ^ 1860 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (1861 : ℕ) - 1 = (2 ^ 2 : ℕ) * ((3 ^ 1 : ℕ) * ((5 ^ 1 : ℕ) * ((31 ^ 1 : ℕ)))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (2 : ZMod 1861) ^ 930 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 3 := prime_eq_of_dvd_power hq prime_3 h1
      subst q
      change (2 : ZMod 1861) ^ 620 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 5 := prime_eq_of_dvd_power hq prime_5 h2
      subst q
      change (2 : ZMod 1861) ^ 372 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 31 := prime_eq_of_dvd_power hq prime_31 h3
      subst q
      change (2 : ZMod 1861) ^ 60 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_13463 : Nat.Prime 13463 := by
  apply lucas_primality 13463 5
  · change (5 : ZMod 13463) ^ 13462 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (13463 : ℕ) - 1 = (2 ^ 1 : ℕ) * ((53 ^ 1 : ℕ) * ((127 ^ 1 : ℕ))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (5 : ZMod 13463) ^ 6731 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 53 := prime_eq_of_dvd_power hq prime_53 h1
      subst q
      change (5 : ZMod 13463) ^ 254 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 127 := prime_eq_of_dvd_power hq prime_127 h2
      subst q
      change (5 : ZMod 13463) ^ 106 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_17863 : Nat.Prime 17863 := by
  apply lucas_primality 17863 6
  · change (6 : ZMod 17863) ^ 17862 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (17863 : ℕ) - 1 = (2 ^ 1 : ℕ) * ((3 ^ 1 : ℕ) * ((13 ^ 1 : ℕ) * ((229 ^ 1 : ℕ)))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (6 : ZMod 17863) ^ 8931 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 3 := prime_eq_of_dvd_power hq prime_3 h1
      subst q
      change (6 : ZMod 17863) ^ 5954 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 13 := prime_eq_of_dvd_power hq prime_13 h2
      subst q
      change (6 : ZMod 17863) ^ 1374 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 229 := prime_eq_of_dvd_power hq prime_229 h3
      subst q
      change (6 : ZMod 17863) ^ 78 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_29021 : Nat.Prime 29021 := by
  apply lucas_primality 29021 2
  · change (2 : ZMod 29021) ^ 29020 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (29021 : ℕ) - 1 = (2 ^ 2 : ℕ) * ((5 ^ 1 : ℕ) * ((1451 ^ 1 : ℕ))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (2 : ZMod 29021) ^ 14510 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 5 := prime_eq_of_dvd_power hq prime_5 h1
      subst q
      change (2 : ZMod 29021) ^ 5804 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 1451 := prime_eq_of_dvd_power hq prime_1451 h2
      subst q
      change (2 : ZMod 29021) ^ 20 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_58043 : Nat.Prime 58043 := by
  apply lucas_primality 58043 2
  · change (2 : ZMod 58043) ^ 58042 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (58043 : ℕ) - 1 = (2 ^ 1 : ℕ) * ((29021 ^ 1 : ℕ)) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (2 : ZMod 58043) ^ 29021 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 29021 := prime_eq_of_dvd_power hq prime_29021 h1
      subst q
      change (2 : ZMod 58043) ^ 2 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_61813 : Nat.Prime 61813 := by
  apply lucas_primality 61813 2
  · change (2 : ZMod 61813) ^ 61812 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (61813 : ℕ) - 1 = (2 ^ 2 : ℕ) * ((3 ^ 2 : ℕ) * ((17 ^ 1 : ℕ) * ((101 ^ 1 : ℕ)))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (2 : ZMod 61813) ^ 30906 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 3 := prime_eq_of_dvd_power hq prime_3 h1
      subst q
      change (2 : ZMod 61813) ^ 20604 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 17 := prime_eq_of_dvd_power hq prime_17 h2
      subst q
      change (2 : ZMod 61813) ^ 3636 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 101 := prime_eq_of_dvd_power hq prime_101 h3
      subst q
      change (2 : ZMod 61813) ^ 612 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_71453 : Nat.Prime 71453 := by
  apply lucas_primality 71453 2
  · change (2 : ZMod 71453) ^ 71452 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (71453 : ℕ) - 1 = (2 ^ 2 : ℕ) * ((17863 ^ 1 : ℕ)) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (2 : ZMod 71453) ^ 35726 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 17863 := prime_eq_of_dvd_power hq prime_17863 h1
      subst q
      change (2 : ZMod 71453) ^ 4 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_142907 : Nat.Prime 142907 := by
  apply lucas_primality 142907 2
  · change (2 : ZMod 142907) ^ 142906 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (142907 : ℕ) - 1 = (2 ^ 1 : ℕ) * ((71453 ^ 1 : ℕ)) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (2 : ZMod 142907) ^ 71453 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 71453 := prime_eq_of_dvd_power hq prime_71453 h1
      subst q
      change (2 : ZMod 142907) ^ 2 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_178481 : Nat.Prime 178481 := by
  apply lucas_primality 178481 3
  · change (3 : ZMod 178481) ^ 178480 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (178481 : ℕ) - 1 = (2 ^ 4 : ℕ) * ((5 ^ 1 : ℕ) * ((23 ^ 1 : ℕ) * ((97 ^ 1 : ℕ)))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (3 : ZMod 178481) ^ 89240 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 5 := prime_eq_of_dvd_power hq prime_5 h1
      subst q
      change (3 : ZMod 178481) ^ 35696 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 23 := prime_eq_of_dvd_power hq prime_23 h2
      subst q
      change (3 : ZMod 178481) ^ 7760 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 97 := prime_eq_of_dvd_power hq prime_97 h3
      subst q
      change (3 : ZMod 178481) ^ 1840 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_370879 : Nat.Prime 370879 := by
  apply lucas_primality 370879 6
  · change (6 : ZMod 370879) ^ 370878 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (370879 : ℕ) - 1 = (2 ^ 1 : ℕ) * ((3 ^ 1 : ℕ) * ((61813 ^ 1 : ℕ))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (6 : ZMod 370879) ^ 185439 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 3 := prime_eq_of_dvd_power hq prime_3 h1
      subst q
      change (6 : ZMod 370879) ^ 123626 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 61813 := prime_eq_of_dvd_power hq prime_61813 h2
      subst q
      change (6 : ZMod 370879) ^ 6 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_5337349 : Nat.Prime 5337349 := by
  apply lucas_primality 5337349 2
  · change (2 : ZMod 5337349) ^ 5337348 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (5337349 : ℕ) - 1 = (2 ^ 2 : ℕ) * ((3 ^ 1 : ℕ) * ((239 ^ 1 : ℕ) * ((1861 ^ 1 : ℕ)))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (2 : ZMod 5337349) ^ 2668674 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 3 := prime_eq_of_dvd_power hq prime_3 h1
      subst q
      change (2 : ZMod 5337349) ^ 1779116 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 239 := prime_eq_of_dvd_power hq prime_239 h2
      subst q
      change (2 : ZMod 5337349) ^ 22332 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 1861 := prime_eq_of_dvd_power hq prime_1861 h3
      subst q
      change (2 : ZMod 5337349) ^ 2868 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_14216929 : Nat.Prime 14216929 := by
  apply lucas_primality 14216929 7
  · change (7 : ZMod 14216929) ^ 14216928 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (14216929 : ℕ) - 1 = (2 ^ 5 : ℕ) * ((3 ^ 1 : ℕ) * ((11 ^ 1 : ℕ) * ((13463 ^ 1 : ℕ)))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (7 : ZMod 14216929) ^ 7108464 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 3 := prime_eq_of_dvd_power hq prime_3 h1
      subst q
      change (7 : ZMod 14216929) ^ 4738976 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 11 := prime_eq_of_dvd_power hq prime_11 h2
      subst q
      change (7 : ZMod 14216929) ^ 1292448 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 13463 := prime_eq_of_dvd_power hq prime_13463 h3
      subst q
      change (7 : ZMod 14216929) ^ 1056 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_148125737 : Nat.Prime 148125737 := by
  apply lucas_primality 148125737 3
  · change (3 : ZMod 148125737) ^ 148125736 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (148125737 : ℕ) - 1 = (2 ^ 3 : ℕ) * ((11 ^ 1 : ℕ) * ((29 ^ 1 : ℕ) * ((58043 ^ 1 : ℕ)))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (3 : ZMod 148125737) ^ 74062868 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 11 := prime_eq_of_dvd_power hq prime_11 h1
      subst q
      change (3 : ZMod 148125737) ^ 13465976 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 29 := prime_eq_of_dvd_power hq prime_29 h2
      subst q
      change (3 : ZMod 148125737) ^ 5107784 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 58043 := prime_eq_of_dvd_power hq prime_58043 h3
      subst q
      change (3 : ZMod 148125737) ^ 2552 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_1042649473 : Nat.Prime 1042649473 := by
  apply lucas_primality 1042649473 5
  · change (5 : ZMod 1042649473) ^ 1042649472 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (1042649473 : ℕ) - 1 = (2 ^ 7 : ℕ) * ((3 ^ 1 : ℕ) * ((19 ^ 1 : ℕ) * ((142907 ^ 1 : ℕ)))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (5 : ZMod 1042649473) ^ 521324736 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 3 := prime_eq_of_dvd_power hq prime_3 h1
      subst q
      change (5 : ZMod 1042649473) ^ 347549824 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 19 := prime_eq_of_dvd_power hq prime_19 h2
      subst q
      change (5 : ZMod 1042649473) ^ 54876288 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 142907 := prime_eq_of_dvd_power hq prime_142907 h3
      subst q
      change (5 : ZMod 1042649473) ^ 7296 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_4103188409 : Nat.Prime 4103188409 := by
  apply lucas_primality 4103188409 3
  · change (3 : ZMod 4103188409) ^ 4103188408 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (4103188409 : ℕ) - 1 = (2 ^ 3 : ℕ) * ((11 ^ 2 : ℕ) * ((17 ^ 1 : ℕ) * ((23 ^ 1 : ℕ) * ((37 ^ 1 : ℕ) * ((293 ^ 1 : ℕ)))))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3 | h4 | h5
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (3 : ZMod 4103188409) ^ 2051594204 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 11 := prime_eq_of_dvd_power hq prime_11 h1
      subst q
      change (3 : ZMod 4103188409) ^ 373017128 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 17 := prime_eq_of_dvd_power hq prime_17 h2
      subst q
      change (3 : ZMod 4103188409) ^ 241364024 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 23 := prime_eq_of_dvd_power hq prime_23 h3
      subst q
      change (3 : ZMod 4103188409) ^ 178399496 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 37 := prime_eq_of_dvd_power hq prime_37 h4
      subst q
      change (3 : ZMod 4103188409) ^ 110896984 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 293 := prime_eq_of_dvd_power hq prime_293 h5
      subst q
      change (3 : ZMod 4103188409) ^ 14004056 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_187810636613 : Nat.Prime 187810636613 := by
  apply lucas_primality 187810636613 2
  · change (2 : ZMod 187810636613) ^ 187810636612 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (187810636613 : ℕ) - 1 = (2 ^ 2 : ℕ) * ((19 ^ 1 : ℕ) * ((463 ^ 1 : ℕ) * ((5337349 ^ 1 : ℕ)))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (2 : ZMod 187810636613) ^ 93905318306 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 19 := prime_eq_of_dvd_power hq prime_19 h1
      subst q
      change (2 : ZMod 187810636613) ^ 9884770348 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 463 := prime_eq_of_dvd_power hq prime_463 h2
      subst q
      change (2 : ZMod 187810636613) ^ 405638524 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 5337349 := prime_eq_of_dvd_power hq prime_5337349 h3
      subst q
      change (2 : ZMod 187810636613) ^ 35188 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_199957736328435366769577 : Nat.Prime 199957736328435366769577 := by
  apply lucas_primality 199957736328435366769577 3
  · change (3 : ZMod 199957736328435366769577) ^ 199957736328435366769576 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (199957736328435366769577 : ℕ) - 1 = (2 ^ 3 : ℕ) * ((11 ^ 1 : ℕ) * ((23 ^ 1 : ℕ) * ((37 ^ 1 : ℕ) * ((14216929 ^ 1 : ℕ) * ((187810636613 ^ 1 : ℕ)))))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3 | h4 | h5
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (3 : ZMod 199957736328435366769577) ^ 99978868164217683384788 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 11 := prime_eq_of_dvd_power hq prime_11 h1
      subst q
      change (3 : ZMod 199957736328435366769577) ^ 18177976029857760615416 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 23 := prime_eq_of_dvd_power hq prime_23 h2
      subst q
      change (3 : ZMod 199957736328435366769577) ^ 8693814622975450729112 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 37 := prime_eq_of_dvd_power hq prime_37 h3
      subst q
      change (3 : ZMod 199957736328435366769577) ^ 5404263144011766669448 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 14216929 := prime_eq_of_dvd_power hq prime_14216929 h4
      subst q
      change (3 : ZMod 199957736328435366769577) ^ 14064762954674344 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 187810636613 := prime_eq_of_dvd_power hq prime_187810636613 h5
      subst q
      change (3 : ZMod 199957736328435366769577) ^ 1064677378952 ≠ 1
      reduce_mod_char
      decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_44667711762797798403039426178361 : Nat.Prime 44667711762797798403039426178361 := by
  apply lucas_primality 44667711762797798403039426178361 21
  · change (21 : ZMod 44667711762797798403039426178361) ^ 44667711762797798403039426178360 = 1
    reduce_mod_char
  · intro q hq hdiv
    have hpred : (44667711762797798403039426178361 : ℕ) - 1 = (2 ^ 3 : ℕ) * ((5 ^ 1 : ℕ) * ((11 ^ 1 : ℕ) * ((23 ^ 1 : ℕ) * ((251 ^ 1 : ℕ) * ((307 ^ 1 : ℕ) * ((370879 ^ 1 : ℕ) * ((148125737 ^ 1 : ℕ) * ((1042649473 ^ 1 : ℕ))))))))) := by decide
    rw [hpred] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · have he : q = 2 := prime_eq_of_dvd_power hq prime_2 h0
      subst q
      change (21 : ZMod 44667711762797798403039426178361) ^ 22333855881398899201519713089180 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 5 := prime_eq_of_dvd_power hq prime_5 h1
      subst q
      change (21 : ZMod 44667711762797798403039426178361) ^ 8933542352559559680607885235672 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 11 := prime_eq_of_dvd_power hq prime_11 h2
      subst q
      change (21 : ZMod 44667711762797798403039426178361) ^ 4060701069345254400276311470760 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 23 := prime_eq_of_dvd_power hq prime_23 h3
      subst q
      change (21 : ZMod 44667711762797798403039426178361) ^ 1942074424469469495784322877320 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 251 := prime_eq_of_dvd_power hq prime_251 h4
      subst q
      change (21 : ZMod 44667711762797798403039426178361) ^ 177959011007162543438404088360 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 307 := prime_eq_of_dvd_power hq prime_307 h5
      subst q
      change (21 : ZMod 44667711762797798403039426178361) ^ 145497432452110092518043733480 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 370879 := prime_eq_of_dvd_power hq prime_370879 h6
      subst q
      change (21 : ZMod 44667711762797798403039426178361) ^ 120437425043741485506160840 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 148125737 := prime_eq_of_dvd_power hq prime_148125737 h7
      subst q
      change (21 : ZMod 44667711762797798403039426178361) ^ 301552671854708128156280 ≠ 1
      reduce_mod_char
      decide
    · have he : q = 1042649473 := prime_eq_of_dvd_power hq prime_1042649473 h8
      subst q
      change (21 : ZMod 44667711762797798403039426178361) ^ 42840583455411959339320 ≠ 1
      reduce_mod_char
      decide

private theorem count_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p ^ k).divisors.card = k + 1 := by
  rw [Nat.divisors_prime_pow hp]
  simp

private theorem count_prime {p : ℕ} (hp : p.Prime) : p.divisors.card = 2 := by
  simpa using count_prime_pow hp 1

private abbrev mersenneWitness : ℕ := 2 ^ 253 - 1

private theorem witness_factors : mersenneWitness = 23 ^ 2 * (47 * (89 * (178481 * (4103188409 * (199957736328435366769577 * (44667711762797798403039426178361)))))) := by
  norm_num [mersenneWitness]

private theorem hc0 : Nat.Coprime (23 ^ 2) (47 * (89 * (178481 * (4103188409 * (199957736328435366769577 * (44667711762797798403039426178361)))))) := by
  norm_num [Nat.Coprime]

private theorem hc1 : Nat.Coprime (47) (89 * (178481 * (4103188409 * (199957736328435366769577 * (44667711762797798403039426178361))))) := by
  norm_num [Nat.Coprime]

private theorem hc2 : Nat.Coprime (89) (178481 * (4103188409 * (199957736328435366769577 * (44667711762797798403039426178361)))) := by
  norm_num [Nat.Coprime]

private theorem hc3 : Nat.Coprime (178481) (4103188409 * (199957736328435366769577 * (44667711762797798403039426178361))) := by
  norm_num [Nat.Coprime]

private theorem hc4 : Nat.Coprime (4103188409) (199957736328435366769577 * (44667711762797798403039426178361)) := by
  norm_num [Nat.Coprime]

private theorem hc5 : Nat.Coprime (199957736328435366769577) (44667711762797798403039426178361) := by
  norm_num [Nat.Coprime]

private theorem count_mul {m n cm cn : ℕ} (h : m.Coprime n)
    (hm : m.divisors.card = cm) (hn : n.divisors.card = cn) :
    (m * n).divisors.card = cm * cn :=
  h.card_divisors_mul.trans (congrArg₂ (· * ·) hm hn)

private theorem totient_mul_known {m n tm tn : ℕ} (h : m.Coprime n)
    (hm : Nat.totient m = tm) (hn : Nat.totient n = tn) :
    Nat.totient (m * n) = tm * tn :=
  (Nat.totient_mul h).trans (congrArg₂ (· * ·) hm hn)

private theorem witness_count : mersenneWitness.divisors.card = 192 := by
  exact (congrArg (fun m : ℕ => m.divisors.card) witness_factors).trans
    ((count_mul hc0 (count_prime_pow prime_23 2)
      (count_mul hc1 (count_prime prime_47)
        (count_mul hc2 (count_prime prime_89)
          (count_mul hc3 (count_prime prime_178481)
            (count_mul hc4 (count_prime prime_4103188409)
              (count_mul hc5 (count_prime prime_199957736328435366769577)
                (count_prime prime_44667711762797798403039426178361))))))).trans (by norm_num))

private theorem witness_totient :
    Nat.totient mersenneWitness = 13397814290058187027242671731749193613131906375649571298061920000991343411200 := by
  exact (congrArg Nat.totient witness_factors).trans
    ((totient_mul_known hc0 (Nat.totient_prime_pow_succ prime_23 1)
      (totient_mul_known hc1 (Nat.totient_prime prime_47)
        (totient_mul_known hc2 (Nat.totient_prime prime_89)
          (totient_mul_known hc3 (Nat.totient_prime prime_178481)
            (totient_mul_known hc4 (Nat.totient_prime prime_4103188409)
              (totient_mul_known hc5 (Nat.totient_prime prime_199957736328435366769577)
                (Nat.totient_prime prime_44667711762797798403039426178361))))))).trans (by norm_num))

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_254323.main) := by
  intro claim
  have h := claim 253 (by decide)
  change mersenneWitness.divisors.card ∣ Nat.totient mersenneWitness at h
  rw [witness_count, witness_totient, Nat.dvd_iff_mod_eq_zero] at h
  norm_num at h
