import OMAStatements.S_oeis_a351415
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.Irrational

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Preorder.Finite

import Mathlib.Tactic.Positivity

namespace OpenMath.A351415

open Filter Topology

open OMA.S_oeis_a351415 (alpha InBeatty Mem Consecutive)

private theorem alpha_pos : 0 < alpha := by
  have hs : (1 : ℝ) < Real.sqrt 5 := Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold alpha
  linarith

private theorem alpha_lt : alpha < 1 := by
  have hs : Real.sqrt 5 < (3 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  unfold alpha
  linarith

private theorem alpha_sq : alpha ^ 2 + alpha = 1 := by
  unfold alpha
  nlinarith [show (Real.sqrt 5) ^ 2 = 5 from Real.sq_sqrt (by norm_num)]

private theorem fib_phase (n : ℕ) :
    (Nat.fib (n + 1) : ℝ) * alpha - (Nat.fib n : ℝ) = (-1 : ℝ) ^ n * alpha ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : (Nat.fib (n + 2) : ℝ) * alpha - (Nat.fib (n + 1) : ℝ) =
        -alpha * ((Nat.fib (n + 1) : ℝ) * alpha - (Nat.fib n : ℝ)) := by
      rw [Nat.fib_add_two, Nat.cast_add]
      linear_combination (Nat.fib (n + 1) : ℝ) * alpha_sq
    change (Nat.fib (n + 2) : ℝ) * alpha - (Nat.fib (n + 1) : ℝ) = _
    rw [hs, ih, pow_succ (-1 : ℝ), pow_succ alpha]
    ring

/-- Every open arc inside [0,1) contains a positive golden-ratio orbit point
with index beyond any prescribed bound. -/
theorem arbitrarily_late_phase (N : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    ∃ k : ℕ, N < k ∧ a < Int.fract ((k : ℝ) * alpha) ∧ Int.fract ((k : ℝ) * alpha) < b := by
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one alpha_pos.le alpha_lt
  have hevent : ∀ᶠ j : ℕ in atTop, alpha ^ j < b - a :=
    hlim.eventually (eventually_lt_nhds (sub_pos.mpr hab))
  obtain ⟨M,hM⟩ := eventually_atTop.mp hevent
  let n := 2 * (M + N + 5)
  let ε := alpha ^ (n + 1)
  let q := Nat.fib (n + 1)
  have hε : 0 < ε := pow_pos alpha_pos _
  have hsmall : ε < b - a := hM _ (by dsimp [n]; omega)
  have hin : Even n := ⟨M + N + 5, by dsimp [n]; omega⟩
  have hf : (q : ℝ) * alpha - (Nat.fib n : ℝ) = ε := by
    have hp := fib_phase n
    change (q : ℝ) * alpha - (Nat.fib n : ℝ) = _
    simpa [q, ε, hin.neg_one_pow] using hp
  have hq : N < q := by
    exact lt_of_lt_of_le (by dsimp [n]; omega) (Nat.le_fib_self (by dsimp [n]; omega))
  let r : ℤ := ⌊a / ε⌋ + 1
  have hr : 0 < r := by
    dsimp [r]
    have hf' : 0 ≤ ⌊a / ε⌋ := Int.floor_nonneg.mpr (div_nonneg ha hε.le)
    omega
  have hrNat : ↑r.toNat = r := Int.toNat_of_nonneg hr.le
  have hrt : (r.toNat : ℝ) = (r : ℝ) := by exact_mod_cast hrNat
  have hlow : a < (r : ℝ) * ε := by
    have hx := (div_lt_iff₀ hε).mp (Int.lt_floor_add_one (a / ε))
    simpa [r] using hx
  have hhigh : (r : ℝ) * ε < b := by
    have hx := (le_div_iff₀ hε).mp (Int.floor_le (a / ε))
    dsimp [r]
    push_cast
    linarith [show ((⌊a / ε⌋ : ℤ) : ℝ) * ε + ε =
      (((⌊a / ε⌋ : ℤ) : ℝ) + 1) * ε by ring]
  let k := q * r.toNat
  have hk : N < k := by
    exact hq.trans_le (by dsimp [k]; exact Nat.le_mul_of_pos_right q (by omega))
  have hexp : (k : ℝ) * alpha = (r : ℝ) * ε +
      (((r * (Nat.fib n : ℤ)) : ℤ) : ℝ) := by
    dsimp [k]
    push_cast
    rw [hrt]
    linear_combination (r : ℝ) * hf
  have hfract : Int.fract ((k : ℝ) * alpha) = (r : ℝ) * ε := by
    rw [hexp, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨ha.trans hlow.le, hhigh.trans_le hb⟩
  exact ⟨k, hk, hfract.symm ▸ hlow, hfract.symm ▸ hhigh⟩


private theorem alpha_mul_phi : (alpha + 1) * alpha = 1 := by
  nlinarith [alpha_sq]

private theorem phi_mul_alpha : alpha * (alpha + 1) = 1 :=
  mul_comm _ _ |>.trans alpha_mul_phi

private theorem inPhi_iff (alpha_irrational : Irrational alpha) (m : ℤ) (hm : 0 < m) :
    InBeatty (alpha + 1) m ↔ 1 - alpha < Int.fract ((m : ℝ) * alpha) := by
  let z : ℝ := (m : ℝ) * alpha
  let f : ℤ := ⌊z⌋
  have hf0 : (f : ℝ) ≤ z := Int.floor_le _
  have hf1 : z < (f : ℝ) + 1 := Int.lt_floor_add_one _
  have hz : Irrational z := alpha_irrational.intCast_mul hm.ne'
  have phi_pos : 0 < alpha + 1 := by linarith [alpha_pos]
  constructor
  · rintro ⟨i,_,hi⟩
    obtain ⟨hi0,hi1⟩ := Int.floor_eq_iff.mp hi
    have hlow : z ≤ (i : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right hi0 alpha_pos.le
      simpa only [mul_assoc, alpha_mul_phi, mul_one] using hh
    have hhigh : (i : ℝ) < z + alpha := by
      have hh := mul_lt_mul_of_pos_right hi1 alpha_pos
      rw [mul_assoc, alpha_mul_phi, mul_one, add_mul, one_mul] at hh
      exact hh
    have hl : (f : ℝ) < (i : ℝ) :=
      hf0.trans_lt (lt_of_le_of_ne hlow (hz.ne_nat i))
    have hil : f < (i : ℤ) := by exact_mod_cast hl
    have hil' : (f : ℝ) + 1 ≤ (i : ℝ) := by
      exact_mod_cast (show f + 1 ≤ (i : ℤ) by omega)
    change 1 - alpha < z - (f : ℝ)
    linarith
  · intro hh
    change 1 - alpha < z - (f : ℝ) at hh
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hf : 0 ≤ f := Int.floor_nonneg.mpr (mul_nonneg hm'.le alpha_pos.le)
    let i : ℕ := (f + 1).toNat
    have hic : (i : ℝ) = (f : ℝ) + 1 := by
      have hi' := Int.toNat_of_nonneg (show 0 ≤ f + 1 by omega)
      exact_mod_cast hi'
    have hip : 0 < i := by
      have hh' : (0 : ℝ) < i := by rw [hic]; exact_mod_cast (show 0 < f + 1 by omega)
      exact_mod_cast hh'
    refine ⟨i,hip,Int.floor_eq_iff.mpr ⟨?_,?_⟩⟩
    · have hlow : z ≤ (i : ℝ) := by rw [hic]; exact hf1.le
      have hz' := mul_le_mul_of_nonneg_right hlow phi_pos.le
      simpa only [z, mul_assoc, phi_mul_alpha, mul_one] using hz'
    · have hhigh : (i : ℝ) < z + alpha := by rw [hic]; linarith
      have hz' := mul_lt_mul_of_pos_right hhigh phi_pos
      simpa only [z, add_mul, mul_assoc, phi_mul_alpha, mul_one] using hz'


private noncomputable def root := Real.sqrt 5
private noncomputable def b := root / 5
private noncomputable def a := (1 - b) / 2

private theorem root_sq : root ^ 2 = 5 := Real.sq_sqrt (by norm_num)
private theorem root_lo : (2236 / 1000 : ℝ) < root :=
  Real.lt_sqrt_of_sq_lt (by norm_num)
private theorem root_hi : root < (2237 / 1000 : ℝ) :=
  (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)

private theorem root_irr : Irrational root := by
  simpa [root] using (show Nat.Prime 5 by decide).irrational_sqrt

private theorem alpha_irr : Irrational alpha := by
  simpa [alpha, root] using (root_irr.sub_intCast 1).div_intCast (m := 2) (by decide)

private theorem frac_as {x : ℝ} {q : ℤ} (hl : (q : ℝ) ≤ x) (hu : x < (q : ℝ) + 1) :
    Int.fract x = x - (q : ℝ) := by
  unfold Int.fract
  rw [Int.floor_eq_iff.mpr ⟨hl, hu⟩]

private theorem root_slope_pos : 0 < root / 2 := by linarith [root_lo]
private theorem root_slope_times_b : root / 2 * b = 1 / 2 := by
  unfold b
  nlinarith [root_sq]

private theorem root_slope_times_two_b : root / 2 * (2 * b) = 1 := by
  linear_combination 2 * root_slope_times_b

private theorem root_slope_times_one_sub_b : root / 2 * (1 - b) = alpha := by
  change root / 2 * (1 - b) = (root - 1) / 2
  linear_combination -root_slope_times_b

private theorem root_slope_times_one_sub_two_b : root / 2 * (1 - 2 * b) = alpha - 1 / 2 := by
  change root / 2 * (1 - 2 * b) = (root - 1) / 2 - 1 / 2
  linear_combination -2 * root_slope_times_b

private theorem positive_fraction_even {y : ℝ} (hy : 0 < y) (hy' : y < 1) (hb : y ≠ 2 * b) :
    1 - alpha < Int.fract (-(root / 2 * y)) ↔ y < 1 - b ∨ 2 * b < y := by
  have halpha : alpha = (root - 1) / 2 := rfl
  by_cases hsmall : y < 2 * b
  · have hlow := mul_pos root_slope_pos hy
    have hhigh := mul_lt_mul_of_pos_left hsmall root_slope_pos
    rw [root_slope_times_two_b] at hhigh
    rw [frac_as (q := -1) (by norm_num; linarith) (by norm_num; linarith)]
    norm_num
    have he : y < 1 - b ↔ root / 2 * y < alpha := by
      rw [← root_slope_times_one_sub_b]
      exact ⟨fun hl => mul_lt_mul_of_pos_left hl root_slope_pos,
        fun hl => lt_of_mul_lt_mul_left hl root_slope_pos.le⟩
    constructor
    · intro h
      exact Or.inl (he.mpr (by linarith only [h]))
    · rintro (h | h)
      · linarith only [he.mp h]
      · linarith only [h, hsmall]
  · have hlarge : 2*b < y := lt_of_le_of_ne (le_of_not_gt hsmall) (Ne.symm hb)
    have hlow := mul_lt_mul_of_pos_left hlarge root_slope_pos
    have hhigh := mul_lt_mul_of_pos_left hy' root_slope_pos
    rw [root_slope_times_two_b] at hlow
    rw [mul_one] at hhigh
    rw [frac_as (q := -2) (by norm_num; linarith [root_hi]) (by norm_num; linarith)]
    norm_num
    constructor
    · intro _
      exact Or.inr hlarge
    · intro _
      linarith [hhigh, halpha]

private theorem positive_fraction_odd {y : ℝ} (hy : 0 < y) (hy' : y < 1) (hb : y ≠ b) :
    1 - alpha < Int.fract (-(root / 2 * y) - 1 / 2) ↔ y < 1 - 2 * b ∨ b < y := by
  have halpha : alpha = (root - 1) / 2 := rfl
  by_cases hsmall : y < b
  · have hlow := mul_pos root_slope_pos hy
    have hhigh := mul_lt_mul_of_pos_left hsmall root_slope_pos
    rw [root_slope_times_b] at hhigh
    rw [frac_as (q := -1) (by norm_num; linarith) (by norm_num; linarith)]
    norm_num
    have he : y < 1 - 2 * b ↔ root / 2 * y < alpha - 1/2 := by
      rw [← root_slope_times_one_sub_two_b]
      exact ⟨fun hl => mul_lt_mul_of_pos_left hl root_slope_pos,
        fun hl => lt_of_mul_lt_mul_left hl root_slope_pos.le⟩
    constructor
    · intro h
      exact Or.inl (he.mpr (by linarith only [h]))
    · rintro (h | h)
      · linarith only [he.mp h]
      · linarith only [h, hsmall]
  · have hlarge : b < y := lt_of_le_of_ne (le_of_not_gt hsmall) (Ne.symm hb)
    have hlow := mul_lt_mul_of_pos_left hlarge root_slope_pos
    have hhigh := mul_lt_mul_of_pos_left hy' root_slope_pos
    rw [root_slope_times_b] at hlow
    rw [mul_one] at hhigh
    rw [frac_as (q := -2) (by norm_num; linarith [root_hi]) (by norm_num; linarith)]
    norm_num
    constructor
    · intro _
      exact Or.inr hlarge
    · intro _
      linarith [hhigh, halpha]


private def Arc (t : ℝ) : Prop := t < a ∨ (b < t ∧ t < 1 - b) ∨ 1 - a < t
private noncomputable def phase (k : ℕ) : ℝ := Int.fract ((k : ℝ) * alpha)
private noncomputable def v (k : ℕ) : ℤ := ⌊(k : ℝ) * root⌋

private theorem unreach (k : ℕ) (hk : 0 < k) (r c : ℚ) (hc : c < 1/2) :
    phase k ≠ (r : ℝ) + (c : ℝ) * root := by
  intro he
  let f : ℤ := ⌊(k : ℝ) * alpha⌋
  have hkc : (1 : ℚ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hden : (k : ℚ)/2 - c ≠ 0 := by linarith
  have hden' : (k : ℝ)/2 - (c : ℝ) ≠ 0 := by
    have hcast : (((k : ℚ)/2-c : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hden
    push_cast at hcast
    exact hcast
  apply root_irr.ne_rat ((r + (f : ℚ) + (k : ℚ)/2) / ((k : ℚ)/2 - c))
  change (k : ℝ) * ((root - 1)/2) - (f : ℝ) = (r : ℝ) + (c : ℝ) * root at he
  push_cast
  rw [eq_div_iff hden']
  linarith only [he]

private theorem arc_iff (k : ℕ) (hk : 0 < k) : Mem (v k) ↔ Arc (phase k) := by
  have hva : InBeatty (Real.sqrt 5) (v k) := ⟨k, hk, rfl⟩
  have km : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hv : 0 < v k := by
    apply (show (1 : ℤ) ≤ v k → 0 < v k by omega)
    apply Int.le_floor.mpr
    have hm := mul_le_mul_of_nonneg_right km (by linarith [root_lo] : 0 ≤ root)
    norm_num at hm ⊢
    linarith [root_lo]
  rw [Mem, and_iff_left hva, inPhi_iff alpha_irr _ hv]
  let t := phase k
  let y := Int.fract ((k : ℝ) * root)
  let f : ℤ := ⌊(k : ℝ) * alpha⌋
  let p : ℤ := ⌊2 * t⌋
  have hpos : (k : ℝ) * root = (v k : ℝ) + y := by
    change (k : ℝ)*root = (v k : ℝ) + ((k : ℝ)*root - (v k : ℝ))
    ring
  have hcoords : (k : ℝ) * root = 2 * t + (((2 * f + (k : ℤ)) : ℤ) : ℝ) := by
    have htf : t = (k : ℝ)*alpha - (f : ℝ) := rfl
    rw [htf, show alpha = (root - 1)/2 from rfl]
    push_cast
    ring
  have hV : v k = 2 * f + (k : ℤ) + p := by
    change ⌊(k : ℝ) * root⌋ = _
    rw [hcoords, Int.floor_add_intCast]
    change p + (2*f + (k : ℤ)) = _
    omega
  have hyt : y = 2 * t - (p : ℝ) := by
    change (k : ℝ) * root - (v k : ℝ) = _
    rw [hcoords, hV]
    push_cast
    ring
  have hQ : (v k : ℝ) * alpha = (5 * (k : ℝ) - (v k : ℝ)) / 2 - root/2*y := by
    change (v k : ℝ) * ((root-1)/2) = _
    linear_combination ((k : ℝ)/2) * root_sq - (root/2) * hpos
  have hPhase : Int.fract ((v k : ℝ) * alpha) =
      Int.fract (-(root/2*y) - (p : ℝ)/2) := by
    have he : (v k : ℝ) * alpha = -(root/2*y) - (p : ℝ)/2 + (((2*(k : ℤ)-f) : ℤ) : ℝ) := by
      rw [hQ, hV]
      push_cast
      ring
    rw [he, Int.fract_add_intCast]
  have hy0 : 0 < y := by
    have hn : 0 ≤ y := Int.fract_nonneg _
    by_contra! hy
    exact (root_irr.natCast_mul hk.ne').ne_int (v k) (by linarith only [hn, hy, hpos])
  have hy1 : y < 1 := Int.fract_lt_one _
  have htl : 0 ≤ t := Int.fract_nonneg _
  have htu : t < 1 := Int.fract_lt_one _
  have hp0 : 0 ≤ p := Int.floor_nonneg.mpr (by linarith)
  have hp1 : p < 2 := by
    have h : (p : ℝ) < 2 := lt_of_le_of_lt (Int.floor_le _) (by linarith)
    exact_mod_cast h
  have hb0 : (0 : ℝ) < b := by unfold b; linarith [root_lo]
  have hb1 : b < 1/2 := by unfold b; linarith [root_hi]
  have ha0 : a = (1 - b)/2 := rfl
  rw [hPhase]
  have hp : p = 0 ∨ p = 1 := by omega
  rcases hp with hp | hp
  · rw [hp] at hyt ⊢
    norm_num at hyt ⊢
    have hyt0 : y ≠ 2 * b := by
      intro hh
      apply unreach k hk 0 (1/5) (by norm_num)
      change t = ((0 : ℚ) : ℝ) + (((1/5 : ℚ)) : ℝ) * root
      unfold b at hh
      push_cast
      linarith only [hh, hyt]
    rw [positive_fraction_even hy0 hy1 hyt0]
    have ht1 : t < 1/2 := by linarith only [hyt, hy1]
    unfold Arc
    constructor
    · rintro (h | h)
      · exact Or.inl (by linarith only [h, hyt, ha0])
      · exact Or.inr (Or.inl ⟨by linarith only [h, hyt], by linarith only [ht1, hb1]⟩)
    · rintro (h | ⟨hl,_⟩ | h)
      · exact Or.inl (by linarith only [h, hyt, ha0])
      · exact Or.inr (by linarith only [hl, hyt])
      · exfalso
        linarith only [h, ht1, ha0, hb0]
  · rw [hp] at hyt ⊢
    norm_num at hyt ⊢
    have hyt0 : y ≠ b := by
      intro hh
      apply unreach k hk (1/2) (1/10) (by norm_num)
      change t = (((1/2 : ℚ)) : ℝ) + (((1/10 : ℚ)) : ℝ) * root
      unfold b at hh
      push_cast
      linarith only [hh, hyt]
    rw [positive_fraction_odd hy0 hy1 hyt0]
    have ht0 : 1/2 < t := by linarith only [hyt, hy0]
    unfold Arc
    constructor
    · rintro (h | h)
      · exact Or.inr (Or.inl ⟨by linarith only [ht0, hb1], by linarith only [h, hyt]⟩)
      · exact Or.inr (Or.inr (by linarith only [h, hyt, ha0]))
    · rintro (h | ⟨_,hu⟩ | h)
      · exfalso
        linarith only [h, ht0, ha0, hb0]
      · exact Or.inl (by linarith only [hu, hyt])
      · exact Or.inr (by linarith only [h, hyt, ha0])


private theorem phase_bounds (k : ℕ) : 0 ≤ phase k ∧ phase k < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

private theorem phase_step (k d : ℕ) :
    phase (k + d) = Int.fract (phase k + (d : ℝ) * alpha) := by
  let f : ℤ := ⌊(k : ℝ) * alpha⌋
  have hf : (k : ℝ) * alpha = phase k + (f : ℝ) := by
    change (k : ℝ)*alpha = ((k : ℝ)*alpha - (f : ℝ)) + (f : ℝ)
    ring
  change Int.fract (((k+d : ℕ) : ℝ) * alpha) = _
  rw [Nat.cast_add, add_mul, hf, add_right_comm, Int.fract_add_intCast]

private theorem root_phase (k : ℕ) :
    Int.fract ((k : ℝ) * root) = Int.fract (2 * phase k) := by
  let f : ℤ := ⌊(k : ℝ) * alpha⌋
  have hcoords : (k : ℝ) * root = 2 * phase k + (((2 * f + (k : ℤ)) : ℤ) : ℝ) := by
    have hphase : phase k = (k : ℝ)*alpha - (f : ℝ) := rfl
    rw [hphase, show alpha = (root - 1)/2 from rfl]
    push_cast
    ring
  rw [hcoords, Int.fract_add_intCast]

private theorem jump (k d : ℕ) :
    v (k+d) - v k = ⌊Int.fract (2 * phase k) + (d : ℝ)*root⌋ := by
  have hx : (k : ℝ)*root = Int.fract ((k : ℝ)*root) + (v k : ℝ) := by
    change (k : ℝ)*root = ((k : ℝ)*root - (v k : ℝ)) + (v k : ℝ)
    ring
  change ⌊((k+d : ℕ):ℝ) * root⌋ - v k = _
  rw [Nat.cast_add, add_mul, hx, add_right_comm, Int.floor_add_intCast, root_phase]
  omega

private theorem v_mono : StrictMono v := by
  intro i j hij
  have hij' : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast (show i+1≤j by omega)
  have hmul := mul_le_mul_of_nonneg_right hij' (by linarith [root_lo] : 0 ≤ root)
  have hi : (v i : ℝ) ≤ (i : ℝ)*root := Int.floor_le _
  have h : ((v i + 1 : ℤ):ℝ) ≤ (j : ℝ)*root := by
    push_cast
    linarith [root_lo]
  have hh : v i + 1 ≤ v j := Int.le_floor.mpr h
  omega

private theorem one_small_return (k : ℕ) (hk : 0 < k) (hA : Arc (phase k)) :
    ∃ d : ℕ, (1 ≤ d ∧ d ≤ 3) ∧ Arc (phase (k+d)) ∧ (d=3 → phase k < 1-2*b) := by
  let t := phase k
  have ht0 : 0 ≤ t := (phase_bounds k).1
  have ht1 : t < 1 := (phase_bounds k).2
  have ta : a = (1 - root/5)/2 := rfl
  have tb : b = root/5 := rfl
  have tr : alpha = (root-1)/2 := rfl
  have hc1 : t ≠ 5/2-11*root/10 := by
    have h := unreach k hk (5/2) (-11/10) (by norm_num)
    exact fun he => h (by push_cast; linarith only [he])
  have hc2 : t ≠ 1-2*b := by
    have h := unreach k hk 1 (-2/5) (by norm_num)
    exact fun he => h (by push_cast; linarith only [he, tb])
  have hc3 : t ≠ 3/2-3*root/10 := by
    have h := unreach k hk (3/2) (-3/10) (by norm_num)
    exact fun he => h (by push_cast; linarith only [he])
  have hc4 : t ≠ 5/2-7*root/10 := by
    have h := unreach k hk (5/2) (-7/10) (by norm_num)
    exact fun he => h (by push_cast; linarith only [he])
  change Arc t at hA
  rcases hA with hL | ⟨hML,hMR⟩ | hR
  · by_cases hcut : t < 5/2-11*root/10
    · refine ⟨2, by decide, ?_, by omega⟩
      rw [phase_step]
      have hl : (1 : ℝ) ≤ t+2*alpha := by linarith only [ht0, tr, root_lo]
      have hu : t+2*alpha < (1 : ℝ)+1 := by linarith only [hcut, tr, root_lo]
      rw [frac_as (q := 1) (by norm_num at hl ⊢; exact hl) (by norm_num at hu ⊢; exact hu)]
      exact Or.inl (by norm_num; linarith only [hcut, ta, tr])
    · have hcut' : 5/2-11*root/10<t := lt_of_le_of_ne (le_of_not_gt hcut) (Ne.symm hc1)
      by_cases hmid : t < 1-2*b
      · refine ⟨3, by decide, ?_, fun _ => hmid⟩
        rw [phase_step]
        have hl : (1 : ℝ) ≤ t+3*alpha := by linarith only [ht0, tr, root_lo]
        have hu : t+3*alpha < (1 : ℝ)+1 := by linarith only [hmid, tb, tr, root_hi]
        rw [frac_as (q := 1) (by norm_num at hl ⊢; exact hl) (by norm_num at hu ⊢; exact hu)]
        exact Or.inr (Or.inr (by norm_num; linarith only [hcut', ta, tr, root_lo]))
      · have hmid' : 1-2*b<t := lt_of_le_of_ne (le_of_not_gt hmid) (Ne.symm hc2)
        refine ⟨1, by decide, ?_, by omega⟩
        rw [phase_step]
        have hl : (0 : ℝ) ≤ t+alpha := by linarith only [ht0, alpha_pos]
        have hu : t+alpha < (0 : ℝ)+1 := by linarith only [hL, ta, tr, root_hi]
        rw [frac_as (q := 0) (by norm_num at hl ⊢; exact hl) (by norm_num at hu ⊢; exact hu)]
        exact Or.inr (Or.inr (by norm_num; linarith only [hmid', ta, tb, tr]))
  · refine ⟨1, by decide, ?_, by omega⟩
    rw [phase_step]
    have hl : (1 : ℝ) ≤ t+alpha := by linarith only [hML, tb, tr, root_lo]
    have hu : t+alpha < (1 : ℝ)+1 := by linarith only [hMR, tb, tr, root_hi]
    rw [frac_as (q := 1) (by norm_num at hl ⊢; exact hl) (by norm_num at hu ⊢; exact hu)]
    exact Or.inl (by norm_num; linarith only [hMR, ta, tb, tr, root_hi])
  · by_cases hcut : t < 3/2-3*root/10
    · refine ⟨2, by decide, ?_, by omega⟩
      rw [phase_step]
      by_cases hcross : t+2*alpha < 2
      · have hl : (1 : ℝ) ≤ t+2*alpha := by linarith only [hR, ta, tr, root_lo]
        rw [frac_as (q := 1) (by norm_num at hl ⊢; exact hl) (by norm_num at hcross ⊢; exact hcross)]
        exact Or.inr (Or.inr (by norm_num; linarith only [hR, tr, root_lo]))
      · have hu : t+2*alpha < (2 : ℝ)+1 := by linarith only [hcut, tr, root_hi]
        rw [frac_as (q := 2) (by norm_num; exact le_of_not_gt hcross) (by norm_num at hu ⊢; exact hu)]
        exact Or.inl (by norm_num; linarith only [hcut, ta, tr, root_hi])
    · have hcut' : 3/2-3*root/10 < t := lt_of_le_of_ne (le_of_not_gt hcut) (Ne.symm hc3)
      by_cases hmid : t < 5/2-7*root/10
      · refine ⟨1, by decide, ?_, by omega⟩
        rw [phase_step]
        have hl : (1 : ℝ) ≤ t+alpha := by linarith only [hcut', tr, root_lo]
        have hu : t+alpha < (1 : ℝ)+1 := by linarith only [ht1, alpha_lt]
        rw [frac_as (q := 1) (by norm_num at hl ⊢; exact hl) (by norm_num at hu ⊢; exact hu)]
        exact Or.inr (Or.inl ⟨by norm_num; linarith only [hcut', tr, tb], by norm_num; linarith only [hmid, tr, tb]⟩)
      · have hmid' : 5/2-7*root/10 < t := lt_of_le_of_ne (le_of_not_gt hmid) (Ne.symm hc4)
        refine ⟨2, by decide, ?_, by omega⟩
        rw [phase_step]
        have hl : (2 : ℝ) ≤ t+2*alpha := by linarith only [hmid', tr, root_lo]
        have hu : t+2*alpha < (2 : ℝ)+1 := by linarith only [ht1, alpha_lt]
        rw [frac_as (q := 2) (by norm_num at hl ⊢; exact hl) (by norm_num at hu ⊢; exact hu)]
        exact Or.inl (by norm_num; linarith only [ht1, ta, tr, root_hi])


private theorem sample (g : ℤ) (hg0 : 2 ≤ g) (hg1 : g ≤ 6) :
    ∃ l u : ℝ, 0 ≤ l ∧ l < u ∧ u ≤ 1 ∧
      ∀ t : ℝ, l < t → t < u → Arc t ∧
        ∃ d : ℕ, 0 < d ∧ Arc (Int.fract (t+(d : ℝ)*alpha)) ∧
          (∀ j : ℕ, 0 < j → j < d → ¬Arc (Int.fract (t+(j : ℝ)*alpha))) ∧
          ⌊Int.fract (2*t) + (d : ℝ)*root⌋ = g := by
  have ta : a = (1 - root/5)/2 := rfl
  have tb : b = root/5 := rfl
  have tr : alpha = (root-1)/2 := rfl
  interval_cases g
  · refine ⟨15/100, 16/100, by norm_num, by norm_num, by norm_num, ?_⟩
    intro t hl hu
    refine ⟨?_, ?_⟩
    · exact Or.inl (by linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
    · refine ⟨1, by decide, ?_, ?_, ?_⟩
      · rw [frac_as (q := 0) (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
          (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])]
        exact Or.inr (Or.inr (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu]))
      · intro j h0 h1
        omega
      · rw [frac_as (q := 0) (by norm_num; linarith only [hl, hu])
          (by norm_num; linarith only [hl, hu])]
        apply Int.floor_eq_iff.mpr
        exact ⟨by norm_num; linarith only [root_lo, hl], by norm_num; linarith only [root_hi, hu]⟩
  · refine ⟨47/100, 48/100, by norm_num, by norm_num, by norm_num, ?_⟩
    intro t hl hu
    refine ⟨?_, ?_⟩
    · exact Or.inr (Or.inl ⟨by linarith only [ta, tb, tr, root_lo, root_hi, hl, hu], by linarith only [ta, tb, tr, root_lo, root_hi, hl, hu]⟩)
    · refine ⟨1, by decide, ?_, ?_, ?_⟩
      · rw [frac_as (q := 1) (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
          (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])]
        exact Or.inl (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
      · intro j h0 h1
        omega
      · rw [frac_as (q := 0) (by norm_num; linarith only [hl, hu])
          (by norm_num; linarith only [hl, hu])]
        apply Int.floor_eq_iff.mpr
        exact ⟨by norm_num; linarith only [root_lo, hl], by norm_num; linarith only [root_hi, hu]⟩
  · refine ⟨1/100, 2/100, by norm_num, by norm_num, by norm_num, ?_⟩
    intro t hl hu
    refine ⟨?_, ?_⟩
    · exact Or.inl (by linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
    · refine ⟨2, by decide, ?_, ?_, ?_⟩
      · rw [frac_as (q := 1) (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
          (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])]
        exact Or.inl (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
      · intro j h0 h1
        interval_cases j
        rw [frac_as (q := 0) (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
          (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])]
        rintro (h | ⟨hm,hm'⟩ | h)
        · norm_num at h
          linarith only [ta, tb, tr, root_lo, root_hi, hl, hu, h]
        · norm_num at hm'
          linarith only [ta, tb, tr, root_lo, root_hi, hl, hu, hm']
        · norm_num at h
          linarith only [ta, tb, tr, root_lo, root_hi, hl, hu, h]
      · rw [frac_as (q := 0) (by norm_num; linarith only [hl, hu])
          (by norm_num; linarith only [hl, hu])]
        apply Int.floor_eq_iff.mpr
        exact ⟨by norm_num; linarith only [root_lo, hl], by norm_num; linarith only [root_hi, hu]⟩
  · refine ⟨78/100, 79/100, by norm_num, by norm_num, by norm_num, ?_⟩
    intro t hl hu
    refine ⟨?_, ?_⟩
    · exact Or.inr (Or.inr (by linarith only [ta, tb, tr, root_lo, root_hi, hl, hu]))
    · refine ⟨2, by decide, ?_, ?_, ?_⟩
      · rw [frac_as (q := 2) (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
          (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])]
        exact Or.inl (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
      · intro j h0 h1
        interval_cases j
        rw [frac_as (q := 1) (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
          (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])]
        rintro (h | ⟨hm,hm'⟩ | h)
        · norm_num at h
          linarith only [ta, tb, tr, root_lo, root_hi, hl, hu, h]
        · norm_num at hm
          linarith only [ta, tb, tr, root_lo, root_hi, hl, hu, hm]
        · norm_num at h
          linarith only [ta, tb, tr, root_lo, root_hi, hl, hu, h]
      · rw [frac_as (q := 1) (by norm_num; linarith only [hl, hu])
          (by norm_num; linarith only [hl, hu])]
        apply Int.floor_eq_iff.mpr
        exact ⟨by norm_num; linarith only [root_lo, hl], by norm_num; linarith only [root_hi, hu]⟩
  · refine ⟨5/100, 6/100, by norm_num, by norm_num, by norm_num, ?_⟩
    intro t hl hu
    refine ⟨?_, ?_⟩
    · exact Or.inl (by linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
    · refine ⟨3, by decide, ?_, ?_, ?_⟩
      · rw [frac_as (q := 1) (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
          (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])]
        exact Or.inr (Or.inr (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu]))
      · intro j h0 h1
        interval_cases j
        · rw [frac_as (q := 0) (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
            (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])]
          rintro (h | ⟨hm,hm'⟩ | h)
          · norm_num at h
            linarith only [ta, tb, tr, root_lo, root_hi, hl, hu, h]
          · norm_num at hm'
            linarith only [ta, tb, tr, root_lo, root_hi, hl, hu, hm']
          · norm_num at h
            linarith only [ta, tb, tr, root_lo, root_hi, hl, hu, h]
        · rw [frac_as (q := 1) (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])
            (by norm_num; linarith only [ta, tb, tr, root_lo, root_hi, hl, hu])]
          rintro (h | ⟨hm,hm'⟩ | h)
          · norm_num at h
            linarith only [ta, tb, tr, root_lo, root_hi, hl, hu, h]
          · norm_num at hm
            linarith only [ta, tb, tr, root_lo, root_hi, hl, hu, hm]
          · norm_num at h
            linarith only [ta, tb, tr, root_lo, root_hi, hl, hu, h]
      · rw [frac_as (q := 0) (by norm_num; linarith only [hl, hu])
          (by norm_num; linarith only [hl, hu])]
        apply Int.floor_eq_iff.mpr
        exact ⟨by norm_num; linarith only [root_lo, hl], by norm_num; linarith only [root_hi, hu]⟩


private theorem consecutive_from_index {k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (hx : Arc (phase k)) (hy : Arc (phase (k+d)))
    (hbetween : ∀ j : ℕ, 0 < j → j < d → ¬Arc (phase (k+j))) :
    Consecutive (v k) (v (k+d)) := by
  refine ⟨v_mono (by omega), (arc_iff k hk).mpr hx, (arc_iff (k+d) (by omega)).mpr hy, ?_⟩
  intro z hlo hhi hz
  obtain ⟨i,hi,he⟩ := hz.2
  change v i = z at he
  have hik : k < i := v_mono.lt_iff_lt.mp (by rwa [he])
  have hid : i < k+d := v_mono.lt_iff_lt.mp (by rwa [he])
  have hARC := (arc_iff i hi).mp (he.symm ▸ hz)
  exact hbetween (i-k) (by omega) (by omega) (by rwa [show k+(i-k)=i by omega])

private theorem bounded_gap (x y : ℤ) (h : Consecutive x y) :
    2 ≤ y-x ∧ y-x ≤ 6 := by
  obtain ⟨k,hk,hx⟩ := h.2.1.2
  obtain ⟨i,hi,hy⟩ := h.2.2.1.2
  change v k = x at hx
  change v i = y at hy
  subst x y
  have hki : k < i := v_mono.lt_iff_lt.mp h.1
  let d := i-k
  have hd : 0 < d := by dsimp [d]; omega
  have hid : i = k+d := by dsimp [d]; omega
  have hA := (arc_iff k hk).mp h.2.1
  obtain ⟨e,⟨he,he3⟩,hArc,hcond⟩ := one_small_return k hk hA
  have hde : d ≤ e := by
    by_contra! hbad
    exact h.2.2.2 (v (k+e)) (v_mono (by omega)) (v_mono (by omega))
      ((arc_iff (k+e) (by omega)).mpr hArc)
  rw [hid, jump]
  let w := Int.fract (2*phase k)
  change 2 ≤ ⌊w + (d : ℝ)*root⌋ ∧ ⌊w + (d : ℝ)*root⌋ ≤ 6
  have hw : 0 ≤ w := Int.fract_nonneg _
  have hw' : w < 1 := Int.fract_lt_one _
  have hr : 0 ≤ root := by linarith only [root_lo]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hlo : (2 : ℝ) ≤ w + (d : ℝ)*root := by
    have hp := mul_le_mul_of_nonneg_right hd1 hr
    rw [one_mul] at hp
    linarith only [root_lo, hw, hp]
  have hhi : w + (d : ℝ)*root < 7 := by
    by_cases hd2 : d ≤ 2
    · have hcast : (d : ℝ) ≤ 2 := by exact_mod_cast hd2
      have hp := mul_le_mul_of_nonneg_right hcast hr
      linarith only [hw', root_hi, hp]
    · have heq : d=3 := by omega
      have hbound : phase k < 1-2*b := hcond (by omega)
      have hb : b = root/5 := rfl
      have hf : w = 2 * phase k := by
        apply Int.fract_eq_self.mpr
        exact ⟨by linarith only [(phase_bounds k).1],
          by linarith only [hbound, hb, root_lo]⟩
      rw [hf, heq]
      norm_num
      linarith only [hbound, hb, root_hi]
  have hh : ⌊w + (d : ℝ)*root⌋ < (7 : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hhi)
  exact ⟨Int.le_floor.mpr (by exact_mod_cast hlo), by omega⟩

private theorem v_ge_index (k : ℕ) : (k : ℤ) ≤ v k := by
  apply Int.le_floor.mpr
  push_cast
  have h : (1 : ℝ) ≤ root := by linarith only [root_lo]
  have h' := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ k by positivity)
  rwa [mul_one] at h'

private theorem infinitely_often (g : ℤ) (hg0 : 2 ≤ g) (hg1 : g ≤ 6) :
    {x : ℤ | Consecutive x (x+g)}.Infinite := by
  obtain ⟨a',b',ha,hab,hb,hsample⟩ := sample g hg0 hg1
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨k,hk,hl,hu⟩ := arbitrarily_late_phase N.toNat ha hb hab
  have hk0 : 0 < k := by omega
  have hkN : N < (k : ℤ) := by omega
  obtain ⟨hx,d,hd,htarget,hmid,hg⟩ := hsample (phase k) hl hu
  have hy : Arc (phase (k+d)) := by rwa [phase_step]
  have hmid' (j : ℕ) (hj : 0 < j) (hjd : j < d) : ¬Arc (phase (k+j)) := by
    rw [phase_step]
    exact hmid j hj hjd
  have hcon := consecutive_from_index hk0 hd hx hy hmid'
  have hstep := jump k d
  have hg' : v (k+d) = v k + g := by omega
  rw [hg'] at hcon
  exact ⟨v k, hcon, lt_of_lt_of_le hkN (v_ge_index k)⟩

theorem main :
    (∀ x y : ℤ, Consecutive x y → 2 ≤ y - x ∧ y - x ≤ 6) ∧
    (∀ g : ℤ, 2 ≤ g → g ≤ 6 → {x : ℤ | Consecutive x (x+g)}.Infinite) :=
  ⟨bounded_gap, infinitely_often⟩

end OpenMath.A351415

theorem OMA.solution : type_of% @OMA.S_oeis_a351415.main :=
  OpenMath.A351415.main
