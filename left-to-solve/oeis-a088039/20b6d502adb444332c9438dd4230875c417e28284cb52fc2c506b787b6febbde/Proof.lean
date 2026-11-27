import OMAStatements.S_oeis_a088039
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace OpenMath.A088039

open OMA.S_oeis_a088039 (a candidates)

private theorem cube_sub (k : ℕ) (hk : 1 ≤ k) :
    k ^ 3 - 1 = (k - 1) * (k ^ 2 + k + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h : (j + 1) ^ 3 = j * ((j + 1) ^ 2 + (j + 1) + 1) + 1 := by ring
  simp [Nat.succ_eq_add_one, h]

private theorem quadratic_mod (k m : ℕ) :
    (k ^ 2 + k + 1) % m = ((k % m) ^ 2 + k % m + 1) % m := by
  have h := (Nat.mod_modEq k m).symm
  exact ((h.pow 2).add h).add (Nat.ModEq.refl _)

private theorem two_not_dvd (k : ℕ) : ¬ 2 ∣ k ^ 2 + k + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, quadratic_mod]
  have h : k % 2 < 2 := Nat.mod_lt _ (by decide)
  interval_cases (k % 2) <;> decide

private theorem nine_not_dvd (k : ℕ) : ¬ 9 ∣ k ^ 2 + k + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, quadratic_mod]
  have h : k % 9 < 9 := Nat.mod_lt _ (by decide)
  interval_cases (k % 9) <;> decide

private theorem three_pow_dvd_left (n k : ℕ) (hn : 1 ≤ n)
    (h : 3 ^ n ∣ (k - 1) * (k ^ 2 + k + 1)) :
    3 ^ (n - 1) ∣ k - 1 := by
  have hp : Nat.Prime 3 := by decide
  by_cases h3 : 3 ∣ k ^ 2 + k + 1
  · obtain ⟨e, he⟩ := h3
    have hne : ¬ 3 ∣ e := by
      intro hde
      obtain ⟨t, ht⟩ := hde
      exact nine_not_dvd k ⟨t, by rw [he, ht]; ring⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ, he] at h
    have hd : 3 ^ j ∣ (k - 1) * e := by
      apply Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 3)
      convert h using 1; ring
    simpa using ((hp.coprime_iff_not_dvd.mpr hne).pow_left j).dvd_of_dvd_mul_right hd
  · have hd := ((hp.coprime_iff_not_dvd.mpr h3).pow_left n).dvd_of_dvd_mul_right h
    exact (pow_dvd_pow 3 (by omega : n - 1 ≤ n)).trans hd

private theorem factor_separate (p k : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (hk : 1 ≤ k) (h : p ∣ k - 1) : ¬ p ∣ k ^ 2 + k + 1 := by
  intro hq
  have hrepr : k ^ 2 + k + 1 = (k - 1) * (k + 2) + 3 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    ring
  rw [hrepr] at hq
  have hdiv : p ∣ 3 := by
    simpa using Nat.dvd_sub hq (dvd_mul_of_dvd_left h (k + 2))
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdiv with h1 | h3
  · exact hp.ne_one h1
  · exact hp3 h3

private theorem five_bound (n : ℕ) (hn : 2 ≤ n) :
    4 ^ n + 2 ^ n + 1 < (5 : ℕ) ^ n := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j + 2 := ⟨n - 2, by omega⟩
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show j + 1 + 2 = (j + 2) + 1 by omega, pow_succ (4 : ℕ) (j + 2),
      pow_succ (2 : ℕ) (j + 2), pow_succ (5 : ℕ) (j + 2)]
    omega

private theorem three_bound (n : ℕ) (hn : 3 ≤ n) : 2 ^ n ≤ 3 ^ (n - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j + 3 := ⟨n - 3, by omega⟩
  rw [show j + 3 - 1 = j + 2 by omega, pow_add, pow_add]
  norm_num
  have h1 : (2 : ℕ) ^ j ≤ 3 ^ j := Nat.pow_le_pow_left (by decide) _
  omega

private theorem candidate_lower (n k : ℕ) (hn : 3 ≤ n) (hk : k ∈ candidates n) :
    2 ^ n + 1 ≤ k := by
  by_contra! hsmall
  rcases hk with ⟨hk, b, hb, hd⟩
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd (by omega : b ≠ 1)
  have hpd := (pow_dvd_pow_of_dvd hpdiv n).trans hd
  rw [cube_sub k (by omega)] at hpd
  have hpos : 0 < k - 1 := by omega
  by_cases hp3 : p = 3
  · subst p
    have hh := Nat.le_of_dvd hpos (three_pow_dvd_left n k (by omega) hpd)
    have hh' := three_bound n hn
    omega
  · by_cases hpk : p ∣ k - 1
    · have hnot := factor_separate p k hp hp3 (by omega) hpk
      have hpp := ((hp.coprime_iff_not_dvd.mpr hnot).pow_left n).dvd_of_dvd_mul_right hpd
      have hp2 : 2 ≤ p := hp.two_le
      have hplo := Nat.pow_le_pow_left hp2 n
      have hphi := Nat.le_of_dvd hpos hpp
      omega
    · have hpp := ((hp.coprime_iff_not_dvd.mpr hpk).pow_left n).dvd_of_dvd_mul_left hpd
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact two_not_dvd k ((dvd_pow_self 2 (by omega : n ≠ 0)).trans hpp)
      have hp5 : 5 ≤ p := by
        have hl := hp.two_le
        by_contra! hh
        interval_cases p
        · exact hp2 rfl
        · exact hp3 rfl
        · exact (by decide : ¬Nat.Prime 4) hp
      have hplo := Nat.pow_le_pow_left hp5 n
      have hphi := Nat.le_of_dvd (by omega : 0 < k ^ 2 + k + 1) hpp
      have hsq : k ^ 2 ≤ 4 ^ n := by
        calc
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (by omega) _
          _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]; rfl
      have hf := five_bound n (by omega)
      omega

theorem formula (n : ℕ) (hn : 2 < n) : a n = 2 ^ n + 1 := by
  rw [a, if_neg (by omega)]
  apply IsLeast.csInf_eq
  constructor
  · have h : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    refine ⟨by omega, 2, by decide, ?_⟩
    rw [cube_sub _ (by omega), Nat.add_sub_cancel]
    exact dvd_mul_right _ _
  · intro k hk
    exact candidate_lower n k (by omega) hk

private theorem a_zero : a 0 = 0 := by simp [a]

private theorem a_one : a 1 = 2 := by
  rw [a, if_neg (by decide)]
  apply IsLeast.csInf_eq
  exact ⟨⟨by decide, 7, by decide, by decide⟩, fun k hk => hk.1⟩

private theorem a_two : a 2 = 4 := by
  rw [a, if_neg (by decide)]
  apply IsLeast.csInf_eq
  refine ⟨⟨by decide, 3, by decide, by decide⟩, ?_⟩
  intro k hk
  by_contra! hlt
  rcases hk with ⟨hk, b, hb, hd⟩
  have hk' : 0 < k ^ 3 - 1 := by interval_cases k <;> decide
  have hs := Nat.le_of_dvd hk' hd
  have hu : k ^ 3 - 1 ≤ 26 := by interval_cases k <;> decide
  have hb' : b < 6 := by
    by_contra! hbb
    have hv := Nat.pow_le_pow_left hbb 2
    norm_num at hv
    omega
  interval_cases k <;> interval_cases b <;> norm_num at hd

theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 2 * (a (n - 2) : ℤ) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j + 5 := ⟨n-5, by omega⟩
  rw [show j+5-1=j+4 by omega, show j+5-2=j+3 by omega,
    formula _ (by omega), formula _ (by omega), formula _ (by omega)]
  push_cast
  rw [pow_add, pow_add, pow_add]
  ring

open PowerSeries in
theorem generating_function :
    (1 - X) * (1 - 2 * X) * mk (fun n => (a n : ℤ)) =
      2 * X - 2 * X ^ 2 + X ^ 3 - 2 * X ^ 4 := by
  have hden : ((1 - X) * (1 - 2 * X) : ℤ⟦X⟧) = 1 - C 3 * X ^ 1 + C 2 * X ^ 2 := by
    simp
    ring
  have hnum : (2 * X - 2 * X ^ 2 + X ^ 3 - 2 * X ^ 4 : ℤ⟦X⟧) =
      C 2 * X ^ 1 - C 2 * X ^ 2 + X ^ 3 - C 2 * X ^ 4 := by simp
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n < 5
  · have h3 : a 3 = 9 := by rw [formula 3 (by decide)]; decide
    have h4 : a 4 = 17 := by rw [formula 4 (by decide)]; decide
    interval_cases n <;> norm_num [a_zero, a_one, a_two, h3, h4]
  · have h := recurrence n (by omega)
    simp [show 1 ≤ n by omega, show 2 ≤ n by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega]
    omega

open PowerSeries in
theorem main :
    (∀ n : ℕ, 2 < n → a n = 2 ^ n + 1) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * (a (n-1) : ℤ) - 2 * (a (n-2) : ℤ)) ∧
    ((1 - X) * (1 - 2 * X) * mk (fun n => (a n : ℤ)) =
      2 * X - 2 * X ^ 2 + X ^ 3 - 2 * X ^ 4) :=
  ⟨formula, recurrence, generating_function⟩

end OpenMath.A088039

theorem OMA.solution : type_of% @OMA.S_oeis_a088039.main := OpenMath.A088039.main
