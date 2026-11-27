import OMAStatements.S_oeis_a276674
import Mathlib.NumberTheory.ArithmeticFunction.Carmichael

/-! A positive even gap forces an even modulus. An odd prime factor would make
the Carmichael function even, which gives an odd gap for an odd modulus. -/

open ArithmeticFunction

private theorem totient_double_le (n : ℕ) : (2 * n).totient ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn]
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨j, hj⟩ := even_iff_two_dvd.mp he
      rw [Nat.totient_two_mul_of_even he, hj]
      exact Nat.mul_le_mul_left 2 (ih j (by omega))
    · rw [Nat.totient_two_mul_of_odd ho]
      exact Nat.totient_le n

theorem OMA.solution : type_of% @OMA.S_oeis_a276674.main := by
  intro x m hx hm hgap
  have hct : carmichael x ≤ x.totient :=
    Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) (carmichael_dvd_totient x)
  have hcx : carmichael x ≤ x := hct.trans (Nat.totient_le x)
  have hx2 : 2 ≤ x := by omega
  have heven : Even x := by
    rcases Nat.even_or_odd x with he | ho
    · exact he
    · exfalso
      have hxodd := Nat.odd_iff.mp ho
      obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (by omega : x ≠ 1)
      have hp2 : p ≠ 2 := by
        intro h
        subst p
        have h := Nat.dvd_iff_mod_eq_zero.mp hpx
        omega
      have hcp : carmichael p = p - 1 := by
        simpa only [pow_one, Nat.totient_prime hp] using carmichael_pow_of_prime_ne_two 1 hp hp2
      have hpodd := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
      have hpdvd : 2 ∣ carmichael p := by
        rw [hcp, Nat.dvd_iff_mod_eq_zero]
        omega
      have hcmod := Nat.dvd_iff_mod_eq_zero.mp (hpdvd.trans (carmichael_dvd hpx))
      omega
  obtain ⟨j, hj⟩ := even_iff_two_dvd.mp heven
  have htj : x.totient ≤ j := by
    rw [hj]
    exact totient_double_le j
  omega
