import OMAStatements.S_oeis_a111097
import Mathlib.Tactic

/-! Exact rational comparisons around the maximum-likelihood urn size. -/

namespace OpenMath.A111097

open OMA.S_oeis_a111097

private def cubic (m : ℕ) (x : ℚ) : ℚ :=
  1 - m * x + (m : ℚ) * (m - 1) / 2 * x ^ 2 -
    (m : ℚ) * (m - 1) * (m - 2) / 6 * x ^ 3

private def quartic (m : ℕ) (x : ℚ) : ℚ :=
  cubic m x + (m : ℚ) * (m - 1) * (m - 2) * (m - 3) / 24 * x ^ 4

private theorem falling3_nonneg (m : ℕ) : 0 ≤ (m : ℚ) * (m - 1) * (m - 2) := by
  by_cases h : m < 2
  · interval_cases m <;> norm_num
  · have hm : (2 : ℚ) ≤ m := by exact_mod_cast Nat.le_of_not_gt h
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (by linarith)) (by linarith)

private theorem falling4_nonneg (m : ℕ) : 0 ≤ (m : ℚ) * (m - 1) * (m - 2) * (m - 3) := by
  by_cases h : m < 3
  · interval_cases m <;> norm_num
  · have hm : (3 : ℚ) ≤ m := by exact_mod_cast Nat.le_of_not_gt h
    exact mul_nonneg (falling3_nonneg m) (sub_nonneg.mpr hm)

private theorem truncation (m : ℕ) (x : ℚ) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    cubic m x ≤ (1 - x) ^ m ∧ (1 - x) ^ m ≤ quartic m x := by
  induction m with
  | zero => simp [cubic, quartic]
  | succ m ih =>
      have hxsub : 0 ≤ 1 - x := sub_nonneg.mpr hx'
      have h3 : 0 ≤ (m : ℚ) * (m - 1) * (m - 2) / 6 * x ^ 4 :=
        mul_nonneg (div_nonneg (falling3_nonneg m) (by norm_num)) (pow_nonneg hx _)
      have h4 : 0 ≤ (m : ℚ) * (m - 1) * (m - 2) * (m - 3) / 24 * x ^ 5 :=
        mul_nonneg (div_nonneg (falling4_nonneg m) (by norm_num)) (pow_nonneg hx _)
      have c : cubic m x * (1 - x) = cubic (m + 1) x +
          (m : ℚ) * (m - 1) * (m - 2) / 6 * x ^ 4 := by
        simp only [cubic, Nat.cast_add, Nat.cast_one]
        ring
      have q : quartic m x * (1 - x) = quartic (m + 1) x -
          (m : ℚ) * (m - 1) * (m - 2) * (m - 3) / 24 * x ^ 5 := by
        simp only [quartic, cubic, Nat.cast_add, Nat.cast_one]
        ring
      constructor
      · rw [pow_succ]
        exact le_trans (by rw [c]; exact le_add_of_nonneg_right h3)
          (mul_le_mul_of_nonneg_right ih.1 hxsub)
      · rw [pow_succ]
        exact le_trans (mul_le_mul_of_nonneg_right ih.2 hxsub)
          (by rw [q]; exact sub_le_self _ h4)

private def gap (n : ℕ) (x : ℚ) : ℚ :=
  (n : ℚ) - ∑ k ∈ Finset.range (n + 1), (1 - x) ^ k

private theorem geometric (m : ℕ) (x : ℚ) :
    (1 - x) ^ m = 1 - x * ∑ k ∈ Finset.range m, (1 - x) ^ k := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      linear_combination ih

private theorem gap_eq (n : ℕ) (x : ℚ) :
    x * gap n x = (1 - x) ^ (n + 1) - (1 - n * x) := by
  rw [geometric]
  unfold gap
  ring

private theorem gap_mono {n : ℕ} {x y : ℚ} (hxy : x ≤ y) (hy : y ≤ 1) :
    gap n x ≤ gap n y := by
  unfold gap
  exact sub_le_sub_left (Finset.sum_le_sum fun k _ =>
    pow_le_pow_left₀ (sub_nonneg.mpr hy) (by linarith) k) _

private theorem gap_bounds (n : ℕ) {x : ℚ} (hx : 0 < x) (hx' : x ≤ 1) :
    let A : ℚ := n * (n + 1) / 2
    let b : ℚ := (n - 1) / 3
    let C : ℚ := A * b * (n - 2) / 4
    (-1 + A * x - A * b * x ^ 2 ≤ gap n x ∧
      gap n x ≤ -1 + A * x - A * b * x ^ 2 + C * x ^ 3) := by
  dsimp only []
  have ht := truncation (n + 1) x hx.le hx'
  have hgap := gap_eq n x
  have hc : cubic (n + 1) x - (1 - n * x) = x *
      (-1 + (n : ℚ) * (n + 1) / 2 * x - (n : ℚ) * (n + 1) / 2 * ((n - 1) / 3) * x ^ 2) := by
    simp only [cubic, Nat.cast_add, Nat.cast_one]
    ring
  have hq : quartic (n + 1) x - (1 - n * x) = x *
      (-1 + (n : ℚ) * (n + 1) / 2 * x - (n : ℚ) * (n + 1) / 2 * ((n - 1) / 3) * x ^ 2 +
        (n : ℚ) * (n + 1) / 2 * ((n - 1) / 3) * (n - 2) / 4 * x ^ 3) := by
    simp only [quartic, cubic, Nat.cast_add, Nat.cast_one]
    ring
  constructor
  · have h := sub_le_sub_right ht.1 (1 - (n : ℚ) * x)
    rw [hc, ← hgap] at h
    exact le_of_mul_le_mul_left h hx
  · have h := sub_le_sub_right ht.2 (1 - (n : ℚ) * x)
    rw [hq, ← hgap] at h
    exact le_of_mul_le_mul_left h hx

private theorem threshold_signs (n : ℕ) (hn : 2 ≤ n) :
    let A : ℚ := n * (n + 1) / 2
    gap n (1 / (A - ((n : ℚ) - 1) / 3)) < 0 ∧
      0 < gap n (1 / (A - (n : ℚ) / 3)) := by
  let u : ℚ := n
  let A : ℚ := u * (u + 1) / 2
  let b : ℚ := (u - 1) / 3
  let d : ℚ := u / 3
  let C : ℚ := A * b * (u - 2) / 4
  let s : ℚ := A - b
  let t : ℚ := A - d
  change gap n (1 / s) < 0 ∧ 0 < gap n (1 / t)
  have hu : 2 ≤ u := by
    change (2 : ℚ) ≤ (n : ℚ)
    exact_mod_cast hn
  have hu0 : 0 < u := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hb : 0 < b := by dsimp [b]; linarith
  have hs : 1 < s := by dsimp [s, A, b]; nlinarith [sq_nonneg (u - 2)]
  have ht : 1 < t := by dsimp [t, A, d]; nlinarith [sq_nonneg (u - 2)]
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hsX : 0 < 1 / s := by positivity
  have htX : 0 < 1 / t := by positivity
  have hsX' : 1 / s ≤ 1 := (div_le_iff₀ hs0).2 (by linarith)
  have htX' : 1 / t ≤ 1 := (div_le_iff₀ ht0).2 (by linarith)
  have hsBound := (gap_bounds n hsX hsX').2
  change gap n (1 / s) ≤ -1 + A * (1 / s) - A * b * (1 / s) ^ 2 + C * (1 / s) ^ 3 at hsBound
  have htBound := (gap_bounds n htX htX').1
  change -1 + A * (1 / t) - A * b * (1 / t) ^ 2 ≤ gap n (1 / t) at htBound
  have hsProd : C < b ^ 2 * s := by
    have hA4 : 4 * b < A := by dsimp [A, b]; nlinarith [sq_nonneg (u - 2)]
    have h₁ : C < (3 / 4 : ℚ) * A * b ^ 2 := by
      have h₀ := mul_pos hA hb
      dsimp [C]
      have heq : (3 / 4 : ℚ) * A * b ^ 2 - A * b * (u - 2) / 4 = A * b / 4 := by
        dsimp [b]
        ring
      linarith only [heq, h₀]
    have h₂ : (3 / 4 : ℚ) * A * b ^ 2 < s * b ^ 2 :=
      mul_lt_mul_of_pos_right (by dsimp [s]; linarith) (pow_pos hb _)
    simpa only [mul_comm (b ^ 2)] using h₁.trans h₂
  have htProd : 0 < t / 3 - d * b := by
    dsimp [t, d, A, b]
    nlinarith [sq_nonneg u]
  have hsEq : (-1 + A * (1 / s) - A * b * (1 / s) ^ 2 + C * (1 / s) ^ 3) * s ^ 3 =
      C - b ^ 2 * s := by
    field_simp [ne_of_gt hs0]
    dsimp only [s]
    ring
  have htEq : (-1 + A * (1 / t) - A * b * (1 / t) ^ 2) * t ^ 2 = t / 3 - d * b := by
    field_simp [ne_of_gt ht0]
    dsimp only [t, b, d]
    ring
  constructor
  · apply lt_of_le_of_lt hsBound
    have h : (-1 + A * (1 / s) - A * b * (1 / s) ^ 2 + C * (1 / s) ^ 3) * s ^ 3 < 0 := by
      rw [hsEq]
      exact sub_neg.mpr hsProd
    exact neg_of_mul_neg_left h (pow_nonneg hs0.le _)
  · apply lt_of_lt_of_le _ htBound
    have h : 0 < (-1 + A * (1 / t) - A * b * (1 / t) ^ 2) * t ^ 2 := by
      rw [htEq]
      exact htProd
    exact pos_of_mul_pos_left h (pow_nonneg ht0.le _)

private def mode (n : ℕ) : ℕ := n * (n + 1) / 2 - 1 - (n - 1) / 3

private theorem mode_geometry (n : ℕ) (hn : 2 ≤ n) :
    let A : ℚ := n * (n + 1) / 2
    n ≤ mode n ∧ A - ((n : ℚ) - 1) / 3 ≤ (mode n : ℚ) + 1 ∧
      (mode n : ℚ) ≤ A - (n : ℚ) / 3 := by
  let T : ℕ := n * (n + 1) / 2
  let q : ℕ := (n - 1) / 3
  let A : ℚ := n * (n + 1) / 2
  change n ≤ mode n ∧ A - ((n : ℚ) - 1) / 3 ≤ (mode n : ℚ) + 1 ∧
    (mode n : ℚ) ≤ A - (n : ℚ) / 3
  have hT : (T : ℚ) = A := by
    have hN : T * 2 = n * (n + 1) := Nat.div_mul_cancel (Nat.two_dvd_mul_add_one n)
    have hQ : (T : ℚ) * 2 = (n : ℚ) * ((n : ℚ) + 1) := by exact_mod_cast hN
    dsimp [A]
    linarith only [hQ]
  have hqNat : 3 * q + 1 ≤ n ∧ n ≤ 3 * q + 3 := by dsimp [q]; omega
  have hqLow : 3 * (q : ℚ) + 1 ≤ n := by exact_mod_cast hqNat.1
  have hqHigh : (n : ℚ) ≤ 3 * (q : ℚ) + 3 := by exact_mod_cast hqNat.2
  have hnT : n + 1 + q ≤ T := by
    by_cases h : n = 2
    · subst n
      decide
    · have hn3 : (3 : ℚ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have h : (n : ℚ) + 1 + (q : ℚ) ≤ T := by
        rw [hT]
        dsimp [A]
        nlinarith [sq_nonneg ((n : ℚ) - 3)]
      exact_mod_cast h
  have hm : (mode n : ℚ) = A - 1 - q := by
    change ((T - 1 - q : ℕ) : ℚ) = A - 1 - q
    rw [Nat.cast_sub (by omega : q ≤ T - 1), Nat.cast_sub (by omega : 1 ≤ T), hT]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · change n ≤ T - 1 - q
    omega
  · rw [hm]
    linarith only [hqLow]
  · rw [hm]
    linarith only [hqHigh]

private theorem adjacent_sign (n N : ℕ) (hn : 2 ≤ n) :
    (N < mode n → 0 < gap n (1 / ((N : ℚ) + 1))) ∧
      (mode n ≤ N → gap n (1 / ((N : ℚ) + 1)) < 0) := by
  let A : ℚ := n * (n + 1) / 2
  let s : ℚ := A - ((n : ℚ) - 1) / 3
  let t : ℚ := A - (n : ℚ) / 3
  let w : ℚ := (N : ℚ) + 1
  have hsign : gap n (1 / s) < 0 ∧ 0 < gap n (1 / t) := threshold_signs n hn
  have hmode : n ≤ mode n ∧ s ≤ (mode n : ℚ) + 1 ∧ (mode n : ℚ) ≤ t :=
    mode_geometry n hn
  have hn2 : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hw1 : (1 : ℚ) ≤ w := by
    dsimp [w]
    linarith only [Nat.cast_nonneg (α := ℚ) N]
  have hw0 : 0 < w := by linarith
  have hs1 : 1 ≤ s := by dsimp [s, A]; nlinarith [sq_nonneg ((n : ℚ) - 2)]
  have hs0 : 0 < s := by linarith
  constructor
  · intro h
    have hcast : (N : ℚ) + 1 ≤ (mode n : ℚ) := by exact_mod_cast (show N + 1 ≤ mode n by omega)
    have hwt : w ≤ t := hcast.trans hmode.2.2
    have hX : 1 / t ≤ 1 / w := one_div_le_one_div_of_le hw0 hwt
    exact hsign.2.trans_le (gap_mono hX ((div_le_iff₀ hw0).2 (by simpa using hw1)))
  · intro h
    have hcast : (mode n : ℚ) ≤ (N : ℚ) := by exact_mod_cast h
    have hsw : s ≤ w := hmode.2.1.trans (by dsimp [w]; linarith only [hcast])
    have hX : 1 / w ≤ 1 / s := one_div_le_one_div_of_le hs0 hsw
    exact (gap_mono hX ((div_le_iff₀ hs0).2 (by simpa using hs1))).trans_lt hsign.1

private theorem likelihood_pos {n N : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    0 < likelihood n N := by
  unfold likelihood
  have hdesc := Nat.descFactorial_pos.mpr hN
  have hN0 : 0 < N := hn.trans_le hN
  positivity

private theorem likelihood_step (n N : ℕ) (hn : 0 < n) (hN : n ≤ N) :
    let x : ℚ := 1 / ((N : ℚ) + 1)
    let d : ℚ := 1 - n * x
    0 < x ∧ 0 < d ∧
      likelihood n (N + 1) - likelihood n N = (likelihood n N / d) * (x * gap n x) := by
  let v : ℚ := N
  let w : ℚ := (N : ℚ) + 1
  let x : ℚ := 1 / w
  let d : ℚ := 1 - n * x
  change 0 < x ∧ 0 < d ∧
    likelihood n (N + 1) - likelihood n N = (likelihood n N / d) * (x * gap n x)
  have hN0 : 0 < N := hn.trans_le hN
  have hv0 : 0 < v := by change (0 : ℚ) < (N : ℚ); exact_mod_cast hN0
  have hw0 : 0 < w := by dsimp [w]; positivity
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hc : (n : ℚ) ≤ v := by change (n : ℚ) ≤ (N : ℚ); exact_mod_cast hN
  have hwsub : 0 < w - (n : ℚ) := by change 0 < v + 1 - (n : ℚ); linarith
  have hden : d = (w - (n : ℚ)) / w := by
    dsimp only [d, x]
    field_simp [hw0.ne']
  have hd : 0 < d := hden ▸ div_pos hwsub hw0
  have hbase : 1 - x = v / w := by
    have hw : w = v + 1 := rfl
    dsimp only [x]
    field_simp [hw0.ne']
    linarith only [hw]
  have hfac : (w - (n : ℚ)) * ((N + 1).descFactorial n : ℚ) =
      w * (N.descFactorial n : ℚ) := by
    have h := congrArg (fun a : ℕ => (a : ℚ)) (Nat.succ_descFactorial N n)
    push_cast [Nat.cast_sub (by omega : n ≤ N + 1)] at h
    exact h
  have hstep : likelihood n (N + 1) = likelihood n N / d * (1 - x) ^ (n + 1) := by
    rw [hbase, div_pow, hden]
    unfold likelihood
    push_cast
    change (n : ℚ) * ((N + 1).descFactorial n : ℚ) / w ^ (n + 1) =
      (n : ℚ) * (N.descFactorial n : ℚ) / v ^ (n + 1) / ((w - (n : ℚ)) / w) *
        (v ^ (n + 1) / w ^ (n + 1))
    field_simp [hv0.ne', hw0.ne', hwsub.ne']
    linear_combination hfac
  refine ⟨hx0, hd, ?_⟩
  rw [gap_eq, hstep]
  change likelihood n N / d * (1 - x) ^ (n + 1) - likelihood n N =
    likelihood n N / d * ((1 - x) ^ (n + 1) - d)
  rw [mul_sub, div_mul_cancel₀ _ hd.ne']

private theorem monotone_steps (n N : ℕ) (hn : 2 ≤ n) (hN : n ≤ N) :
    (N < mode n → likelihood n N < likelihood n (N + 1)) ∧
      (mode n ≤ N → likelihood n (N + 1) < likelihood n N) := by
  have hn0 : 0 < n := by omega
  have hL := likelihood_pos hn0 hN
  obtain ⟨hx, hd, hstep⟩ := likelihood_step n N hn0 hN
  obtain ⟨hup, hdown⟩ := adjacent_sign n N hn
  constructor
  · intro h
    apply sub_pos.mp
    rw [hstep]
    exact mul_pos (div_pos hL hd) (mul_pos hx (hup h))
  · intro h
    apply sub_neg.mp
    rw [hstep]
    exact mul_neg_of_pos_of_neg (div_pos hL hd) (mul_neg_of_pos_of_neg hx (hdown h))

private theorem unique_mode (n : ℕ) (hn : 2 ≤ n) (N : ℕ) (hN : N ≠ mode n) :
    likelihood n N < likelihood n (mode n) := by
  have hM := (mode_geometry n hn).1
  have hn0 : 0 < n := by omega
  by_cases hlow : N < n
  · have hzero := Nat.descFactorial_of_lt hlow
    simp only [likelihood, hzero, Nat.cast_zero, mul_zero, zero_div]
    exact likelihood_pos hn0 hM
  have hge : n ≤ N := by omega
  by_cases hlt : N < mode n
  · have hmono : StrictMonoOn (likelihood n) (Set.Icc n (mode n)) :=
      strictMonoOn_of_lt_succ Set.ordConnected_Icc fun k _ hk hk' => by
        have hk'': k + 1 ≤ mode n := hk'.2
        exact (monotone_steps n k hn hk.1).1 (by omega)
    exact hmono ⟨hge, hlt.le⟩ ⟨hM, le_rfl⟩ hlt
  · have hgt : mode n < N := by omega
    have hanti : StrictAntiOn (likelihood n) (Set.Ici (mode n)) :=
      strictAntiOn_of_succ_lt Set.ordConnected_Ici fun k _ hk _ =>
        (monotone_steps n k hn (hM.trans hk)).2 hk
    exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hgt.le) hgt

private theorem a_of_unique {n z : ℕ} (hn : 0 < n) (hz : 0 < z)
    (hmax : ∀ N : ℕ, 0 < N → N ≠ z → likelihood n N < likelihood n z) : a n = z := by
  have hset : {N : ℕ | 0 < N ∧ ∀ K : ℕ, 0 < K → likelihood n K ≤ likelihood n N} = {z} := by
    ext N
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hne
      exact (not_lt_of_ge (h.2 z hz)) (hmax N h.1 hne)
    · intro h
      subst N
      refine ⟨hz, fun K hK => ?_⟩
      by_cases h : K = z
      · subst K
        rfl
      · exact (hmax K hK h).le
  simp [a, hn.ne', hset]

theorem a_one : a 1 = 1 := by
  apply a_of_unique (by decide) (by decide)
  intro N hN hne
  have h : (1 : ℚ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℚ) < N := by linarith
  have hprob : likelihood 1 N = 1 / (N : ℚ) := by
    norm_num [likelihood, Nat.descFactorial_one, pow_two]
  have hone : likelihood 1 1 = 1 := by norm_num [likelihood]
  rw [hprob, hone]
  exact (div_lt_iff₀ hN0).2 (by simpa using h)

theorem a_formula (n : ℕ) (hn : 2 ≤ n) :
    a n = n * (n + 1) / 2 - 1 - (n - 1) / 3 := by
  change a n = mode n
  have hM := (mode_geometry n hn).1
  exact a_of_unique (by omega) (by omega) fun N _ => unique_mode n hn N

end OpenMath.A111097


namespace A111097Series

open OMA.S_oeis_a111097

private def tri (n : ℕ) : ℕ := n * (n + 1) / 2

private theorem tri_step (n : ℕ) : tri (n + 1) = tri n + n + 1 := by
  unfold tri
  rw [show (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) by ring]
  omega

private theorem le_tri (n : ℕ) : n ≤ tri n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [tri_step]
    omega

private theorem a_add (h : ∀ n : ℕ, 2 ≤ n → a n = n*(n+1)/2 - 1 - (n-1)/3)
    (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℤ) + 1 + (((n-1)/3 : ℕ) : ℤ) = (tri n : ℤ) := by
  have htri := le_tri n
  have h' : a n = tri n - 1 - (n-1)/3 := h n hn
  omega

theorem second_diff (h1 : a 1 = 1)
    (h : ∀ n : ℕ, 2 ≤ n → a n = n*(n+1)/2 - 1 - (n-1)/3)
    (n : ℕ) (hn : 0 < n) :
    (a (n + 2) : ℤ) - 2 * (a (n + 1) : ℤ) + (a n : ℤ) = secondDifferenceValue n := by
  by_cases hsmall : n = 1
  · subst n
    norm_num [h1, h 2 (by omega), h 3 (by omega), secondDifferenceValue]
  have H0 := a_add h n (by omega)
  have H1 := a_add h (n + 1) (by omega)
  have H2 := a_add h (n + 2) (by omega)
  have hr := tri_step n
  have hr' := tri_step (n + 1)
  simp only [secondDifferenceValue, if_neg hsmall]
  simp only [Nat.add_assoc, Nat.reduceAdd] at hr'
  by_cases hm0 : n % 3 = 0
  · simp only [if_pos hm0]
    omega
  simp only [if_neg hm0]
  by_cases hm1 : n % 3 = 1
  · simp only [if_pos hm1]
    omega
  simp only [if_neg hm1]
  omega

open PowerSeries in
theorem series (h1 : a 1 = 1)
    (h : ∀ n : ℕ, 2 ≤ n → a n = n*(n+1)/2 - 1 - (n-1)/3) :
    (1 - X)^3 * (1 + X + X^2) * mk (fun n => (a n : ℤ)) =
      (X * (1 + 2*X^2 - X^3 + 2*X^4 - X^5) : ℤ⟦X⟧) := by
  have hden : (1 - X)^3 * (1 + X + X^2) =
      (1 - C 2 * X^1 + X^2 - X^3 + C 2 * X^4 - X^5 : ℤ⟦X⟧) := by norm_num; ring
  have hnum : (X * (1 + 2*X^2 - X^3 + 2*X^4 - X^5) : ℤ⟦X⟧) =
      X^1 + C 2 * X^3 - X^4 + C 2 * X^5 - X^6 := by norm_num; ring
  rw [hden, hnum]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases hn : n < 7
  · have h0 : a 0 = 0 := by simp [a]
    interval_cases n <;>
      norm_num [h0, h1, h 2 (by omega), h 3 (by omega), h 4 (by omega),
        h 5 (by omega), h 6 (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  simp only [if_pos (show 1 ≤ k + 7 by omega), if_pos (show 2 ≤ k + 7 by omega),
    if_pos (show 3 ≤ k + 7 by omega), if_pos (show 4 ≤ k + 7 by omega),
    if_pos (show 5 ≤ k + 7 by omega), if_neg (show k + 7 ≠ 1 by omega),
    if_neg (show k + 7 ≠ 3 by omega), if_neg (show k + 7 ≠ 4 by omega),
    if_neg (show k + 7 ≠ 5 by omega), if_neg (show k + 7 ≠ 6 by omega)]
  have e1 := second_diff h1 h (k + 5) (by omega)
  have e2 := second_diff h1 h (k + 2) (by omega)
  have d_eq : secondDifferenceValue (k + 5) = secondDifferenceValue (k + 2) := by
    have hm : (k + 5) % 3 = (k + 2) % 3 := by omega
    simp [secondDifferenceValue, hm, show k + 5 ≠ 1 by omega, show k + 2 ≠ 1 by omega]
  rw [d_eq] at e1
  change (a (k + 7) : ℤ) - 2 * a (k + 6) + a (k + 5) = _ at e1
  change (a (k + 4) : ℤ) - 2 * a (k + 3) + a (k + 2) = _ at e2
  change (a (k + 7) : ℤ) - 2 * a (k + 6) + a (k + 5) - a (k + 4) +
    2 * a (k + 3) - a (k + 2) = _
  omega

end A111097Series

theorem OMA.solution : type_of% @OMA.S_oeis_a111097.main :=
  ⟨OpenMath.A111097.a_one, OpenMath.A111097.a_formula,
    A111097Series.second_diff OpenMath.A111097.a_one OpenMath.A111097.a_formula,
    A111097Series.series OpenMath.A111097.a_one OpenMath.A111097.a_formula⟩
