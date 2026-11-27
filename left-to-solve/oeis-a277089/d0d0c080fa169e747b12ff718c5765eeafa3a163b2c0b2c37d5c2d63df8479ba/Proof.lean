import OMAStatements.S_oeis_a277089
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A counterexample to the recurrence and generating-function conjectures for
the Pisot sequence L(6,15), OEIS A277089. -/

namespace OpenMath.A277089

/-- The original ceiling sequence, L(6,15). -/
def a : ℕ → ℕ
  | 0 => 6
  | 1 => 15
  | n + 2 => (a (n + 1) ^ 2 + a n - 1) / a n

/-- The separately listed S(6,15) sequence, which uses floor followed by one. -/
def s : ℕ → ℕ
  | 0 => 6
  | 1 => 15
  | n + 2 => s (n + 1) ^ 2 / s n + 1

private def residual44 (seq : ℕ → ℕ) : ℤ :=
  (seq 44 : ℤ) - 3 * (seq 43 : ℤ) + (seq 42 : ℤ) + (seq 40 : ℤ) -
    2 * (seq 38 : ℤ) + 2 * (seq 37 : ℤ)

set_option maxRecDepth 2500 in
set_option maxHeartbeats 6000000 in
private theorem a_witness : a 44 = 5383976035599672794 ∧ residual44 a = 1 := by
  norm_num [residual44, a]

set_option maxRecDepth 2500 in
set_option maxHeartbeats 6000000 in
private theorem s_witness : s 44 = 5383976035599672794 ∧ residual44 s = 1 := by
  norm_num [residual44, s]

theorem ceiling_value : a 44 = 5383976035599672794 := a_witness.1

theorem floor_plus_one_value : s 44 = 5383976035599672794 := s_witness.1

private theorem recurrence_false (seq : ℕ → ℕ) (hres : residual44 seq = 1) :
    ¬ (∀ n : ℕ, 7 ≤ n → (seq n : ℤ) = 3 * (seq (n - 1) : ℤ) - (seq (n - 2) : ℤ) -
      (seq (n - 4) : ℤ) + 2 * (seq (n - 6) : ℤ) - 2 * (seq (n - 7) : ℤ)) := by
  intro h
  have hw := h 44 (by decide)
  norm_num at hw
  unfold residual44 at hres
  omega

theorem linear_recurrence_false :
    ¬ (∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 3 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ) -
      (a (n - 4) : ℤ) + 2 * (a (n - 6) : ℤ) - 2 * (a (n - 7) : ℤ)) :=
  recurrence_false a a_witness.2

open PowerSeries in
private theorem series_coeff44 (seq : ℕ → ℕ) :
    coeff 44 ((1 - X) * (1 - 2 * X - X ^ 2 - X ^ 3 - 2 * X ^ 6) *
      mk (fun n => (seq n : ℤ))) = residual44 seq := by
  have hden : ((1 - X) * (1 - 2 * X - X ^ 2 - X ^ 3 - 2 * X ^ 6) : ℤ⟦X⟧) =
      1 - C 3 * X ^ 1 + X ^ 2 + X ^ 4 - C 2 * X ^ 6 + C 2 * X ^ 7 := by
    simp
    ring
  rw [hden]
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk]
  norm_num [residual44]

open PowerSeries in
private theorem numerator_coeff44 :
    coeff 44 (6 - 3 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 + 3 * X ^ 5 - 5 * X ^ 6 : ℤ⟦X⟧) = 0 := by
  have hnum : (6 - 3 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 + 3 * X ^ 5 - 5 * X ^ 6 : ℤ⟦X⟧) =
      C 6 - C 3 * X ^ 1 - X ^ 2 - C 2 * X ^ 3 + X ^ 4 + C 3 * X ^ 5 - C 5 * X ^ 6 := by simp
  rw [hnum]
  simp only [map_add, map_sub, coeff_C, coeff_C_mul, coeff_X_pow]
  norm_num

open PowerSeries in
private theorem series_false (seq : ℕ → ℕ) (hres : residual44 seq = 1) :
    ¬ ((1 - X) * (1 - 2 * X - X ^ 2 - X ^ 3 - 2 * X ^ 6) *
      mk (fun n => (seq n : ℤ)) = 6 - 3 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 + 3 * X ^ 5 - 5 * X ^ 6) := by
  intro h
  have hw := congrArg (coeff 44) h
  rw [series_coeff44, hres, numerator_coeff44] at hw
  omega

open PowerSeries in
theorem generating_function_false :
    ¬ ((1 - X) * (1 - 2 * X - X ^ 2 - X ^ 3 - 2 * X ^ 6) *
      mk (fun n => (a n : ℤ)) = 6 - 3 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 + 3 * X ^ 5 - 5 * X ^ 6) :=
  series_false a a_witness.2

open PowerSeries in
theorem floor_plus_one_disproof :
    (¬ (∀ n : ℕ, 7 ≤ n → (s n : ℤ) = 3 * (s (n - 1) : ℤ) - (s (n - 2) : ℤ) -
      (s (n - 4) : ℤ) + 2 * (s (n - 6) : ℤ) - 2 * (s (n - 7) : ℤ))) ∧
    (¬ ((1 - X) * (1 - 2 * X - X ^ 2 - X ^ 3 - 2 * X ^ 6) *
      mk (fun n => (s n : ℤ)) = 6 - 3 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 + 3 * X ^ 5 - 5 * X ^ 6)) :=
  ⟨recurrence_false s s_witness.2, series_false s s_witness.2⟩

open PowerSeries in
theorem main :
    ¬ ((∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 3 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ) -
      (a (n - 4) : ℤ) + 2 * (a (n - 6) : ℤ) - 2 * (a (n - 7) : ℤ)) ∧
    ((1 - X) * (1 - 2 * X - X ^ 2 - X ^ 3 - 2 * X ^ 6) *
      mk (fun n => (a n : ℤ)) = 6 - 3 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 + 3 * X ^ 5 - 5 * X ^ 6)) :=
  fun h => linear_recurrence_false h.1

end OpenMath.A277089

private theorem source_a_eq : OMA.S_oeis_a277089.a = OpenMath.A277089.a := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => rfl
      | succ n =>
          cases n with
          | zero => rfl
          | succ k =>
              change (OMA.S_oeis_a277089.a (k + 1) ^ 2 + OMA.S_oeis_a277089.a k - 1) /
                  OMA.S_oeis_a277089.a k =
                (OpenMath.A277089.a (k + 1) ^ 2 + OpenMath.A277089.a k - 1) / OpenMath.A277089.a k
              rw [ih (k + 1) (by omega), ih k (by omega)]

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a277089.main) := by
  rw [source_a_eq]
  exact OpenMath.A277089.main
