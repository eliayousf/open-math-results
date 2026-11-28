import OMAStatements.S_oeis_a281216

/-!
Robert Price introduced the sequence, and Colin Barker conjectured its formulas.
Source: https://oeis.org/A281216
-/

namespace A281216Proof

open OMA.S_oeis_a281216 PowerSeries

private def radius (x y : ℤ) : ℕ := x.natAbs + y.natAbs

private def profile (n r : ℕ) : Prop :=
  r ≤ n ∧ if n % 2 = 0 then r % 4 = n % 4 else r % 2 = 1 ∨ r % 4 = (n - 1) % 4

private instance (n r : ℕ) : Decidable (profile n r) := by
  unfold profile
  infer_instance

private theorem radius_plus (x y : ℤ) :
    radius (x + 1) y = if 0 ≤ x then radius x y + 1 else radius x y - 1 := by
  unfold radius
  split_ifs with hx
  · have h := Int.natAbs_of_nonneg hx
    have h' := Int.natAbs_of_nonneg (show 0 ≤ x + 1 by omega)
    omega
  · have h := Int.ofNat_natAbs_of_nonpos (show x ≤ 0 by omega)
    have h' := Int.ofNat_natAbs_of_nonpos (show x + 1 ≤ 0 by omega)
    omega

private theorem radius_minus (x y : ℤ) :
    radius (x - 1) y = if x ≤ 0 then radius x y + 1 else radius x y - 1 := by
  have h := radius_plus (-x) y
  rw [show -x + 1 = -(x - 1) by omega] at h
  simpa only [radius, Int.natAbs_neg, neg_nonneg] using h

private theorem radius_yplus (x y : ℤ) :
    radius x (y + 1) = if 0 ≤ y then radius x y + 1 else radius x y - 1 := by
  simpa [radius, Nat.add_comm] using radius_plus y x

private theorem radius_yminus (x y : ℤ) :
    radius x (y - 1) = if y ≤ 0 then radius x y + 1 else radius x y - 1 := by
  simpa [radius, Nat.add_comm] using radius_minus y x

private theorem neighbor_profile (n : ℕ) (x y : ℤ) :
    (decide (profile n (radius (x - 1) y)) || decide (profile n (radius (x + 1) y)) ||
      decide (profile n (radius x (y - 1))) || decide (profile n (radius x (y + 1)))) =
    decide (profile n (radius x y + 1) ∨ (0 < radius x y ∧ profile n (radius x y - 1))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, radius_minus, radius_plus, radius_yminus, radius_yplus]
  by_cases hr : radius x y = 0
  · have hz : x = 0 ∧ y = 0 := by simpa [radius] using hr
    obtain ⟨rfl, rfl⟩ := hz
    simp [radius]
  · have hp : 0 < radius x y := by omega
    have hz : ¬ (x = 0 ∧ y = 0) := by
      intro h
      obtain ⟨rfl, rfl⟩ := h
      exact hr (by decide)
    simp only [hp, true_and]
    split_ifs <;> first | tauto | omega

private theorem rule_table : ∀ c d e f g : Bool,
    (342 : ℕ).testBit (c.toNat + 2 * (d.toNat + e.toNat + f.toNat + g.toNat)) =
      Bool.xor c (d || e || f || g) := by decide

set_option maxHeartbeats 800000 in
private theorem profile_step (n r : ℕ) :
    Bool.xor (decide (profile n r))
      (decide (profile n (r + 1) ∨ (0 < r ∧ profile n (r - 1)))) =
      decide (profile (n + 1) r) := by
  by_cases hc : profile n r <;>
    by_cases hnear : profile n (r + 1) ∨ (0 < r ∧ profile n (r - 1)) <;>
    simp [hc, hnear, Bool.xor] <;> unfold profile at * <;> split_ifs at * <;> omega

private theorem state_profile (n : ℕ) (x y : ℤ) :
    state n x y = decide (profile n (radius x y)) := by
  induction n generalizing x y with
  | zero =>
      apply Bool.eq_iff_iff.mpr
      simp [state, profile, radius]
      intro hx hy
      simp [hx, hy]
  | succ n ih =>
      rw [state, rule_table]
      simp only [ih]
      rw [neighbor_profile, profile_step]

private theorem profile_shift (n k : ℕ) : profile (n + 2) (k + 2) ↔ profile n k := by
  unfold profile
  split_ifs <;> omega

private theorem profile_small (n k : ℕ) (hk : k ≤ 1) :
    profile (n + 6) k ↔ profile (n + 2) k := by
  unfold profile
  split_ifs <;> omega

private def low (n : ℕ) : ℕ :=
  (if profile n 0 then 1 else 0) + (if profile n 1 then 2 else 0)

private theorem digit_sum (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), if profile n k then 2 ^ k else 0 := by
  unfold a
  have hr (k : ℕ) : radius (-(k : ℤ)) 0 = k := by simp [radius]
  simp [state_profile, hr]

private theorem step (n : ℕ) : a (n + 2) = 4 * a n + low (n + 2) := by
  rw [digit_sum (n + 2), digit_sum n, Finset.sum_range_succ', Finset.sum_range_succ']
  have hterm (k : ℕ) :
      (if profile (n + 2) (k + 1 + 1) then (2 : ℕ) ^ (k + 1 + 1) else 0) =
        4 * (if profile n k then 2 ^ k else 0) := by
    rw [show k + 1 + 1 = k + 2 by omega]
    by_cases h : profile n k
    · rw [if_pos ((profile_shift n k).2 h), if_pos h, pow_add]
      ring
    · have h' : ¬ profile (n + 2) (k + 2) := fun hp => h ((profile_shift n k).1 hp)
      simp [h, h']
  simp only [hterm, ← Finset.mul_sum]
  norm_num [low, Nat.add_assoc]
  exact Nat.add_comm _ _

private theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 4 * a (n - 2) + a (n - 4) - 4 * a (n - 6) := by
  let k := n - 6
  have hleft : (a (k + 6) : ℤ) = 4 * a (k + 4) + low (k + 6) := by
    exact_mod_cast step (k + 4)
  have hright : (a (k + 2) : ℤ) = 4 * a k + low (k + 2) := by
    exact_mod_cast step k
  have hlow : low (k + 6) = low (k + 2) := by
    simp [low, profile_small k 0 (by decide), profile_small k 1 (by decide)]
  rw [hlow] at hleft
  have h : (a (k + 6) : ℤ) = 4 * a (k + 4) + a (k + 2) - 4 * a k := by
    linarith
  have hk₆ : k + 6 = n := by dsimp [k]; omega
  have hk₄ : k + 4 = n - 2 := by dsimp [k]; omega
  have hk₂ : k + 2 = n - 4 := by dsimp [k]; omega
  simpa only [hk₆, hk₄, hk₂] using h

private theorem generating_function :
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) *
      (1 + X ^ 2)) = 1 + 3 * X + 2 * X ^ 3 := by
  let A : ℤ⟦X⟧ := mk (fun n => (a n : ℤ))
  have hC (k : ℕ) : C (k : ℤ) = (k : ℤ⟦X⟧) := map_natCast C k
  have hc₂ : C (2 : ℤ) = (2 : ℤ⟦X⟧) := hC 2
  have hc₃ : C (3 : ℤ) = (3 : ℤ⟦X⟧) := hC 3
  have hc₄ : C (4 : ℤ) = (4 : ℤ⟦X⟧) := hC 4
  change A * _ = _
  have heq : A * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + X ^ 2)) =
      A - C 4 * (X ^ 2 * A) - X ^ 4 * A + C 4 * (X ^ 6 * A) := by
    rw [hc₄]
    ring
  rw [heq, ← hc₂, ← hc₃]
  ext n
  by_cases hn : 5 < n
  · have h₂ : 2 ≤ n := by omega
    have h₄ : 4 ≤ n := by omega
    have h₆ : 6 ≤ n := by omega
    have hn₀ : n ≠ 0 := by omega
    have hn₁ : n ≠ 1 := by omega
    have hn₃ : n ≠ 3 := by omega
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', if_pos h₂, if_pos h₄, if_pos h₆,
      coeff_X, coeff_one, coeff_X_pow, if_neg hn₀, if_neg hn₁, if_neg hn₃,
      mul_zero, add_zero, A, coeff_mk]
    linarith [recurrence n hn]
  · have a₀ : a 0 = 1 := by decide
    have a₁ : a 1 = 3 := by decide
    have a₂ : a 2 = 4 := by decide
    have a₃ : a 3 = 14 := by decide
    have a₄ : a 4 = 17 := by
      have h := step 2
      norm_num [a₂, low, profile] at h
      exact h
    have a₅ : a 5 = 59 := by
      have h := step 3
      norm_num [a₃, low, profile] at h
      exact h
    interval_cases n <;>
      simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X, coeff_X_pow,
        coeff_one, A, coeff_mk] <;>
      norm_num [a₀, a₁, a₂, a₃, a₄, a₅]

end A281216Proof

open A281216Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a281216.main :=
  ⟨recurrence, generating_function⟩
