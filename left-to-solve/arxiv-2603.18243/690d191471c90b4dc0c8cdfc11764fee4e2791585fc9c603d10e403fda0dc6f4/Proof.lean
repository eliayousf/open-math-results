import OMAStatements.S_arxiv_2603_18243

open Filter OMA.S_arxiv_2603_18243
open scoped Topology

namespace HymanDensity

private theorem near_power_persistent (k b : ℕ)
    (hlo : 100000000 * 10 ^ k < b) (hhi : b ≤ 100000000 * 10 ^ k + 10 ^ k + 1) :
    persistent 10000 b := by
  let t : ℝ := 10 ^ k
  let base : ℝ := 100000000 * t
  let ratio : ℝ := b / base
  let r := Real.log ratio / Real.log 10
  have ht : 1 ≤ t := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10)
  have hbase : 0 < base := by dsimp [base]; positivity
  have hbLo : base < (b : ℝ) := by
    dsimp [base, t]
    exact_mod_cast hlo
  have hbHi : (b : ℝ) ≤ base + t + 1 := by
    dsimp [base, t]
    exact_mod_cast hhi
  have hratioLo : 1 < ratio := (lt_div_iff₀ hbase).mpr (by simpa using hbLo)
  have hratioHi : ratio ≤ 1 + 1 / 50000000 := by
    apply (div_le_iff₀ hbase).mpr
    dsimp [base] at *
    linarith
  have hlogLo : 9 / 10 ≤ Real.log (10 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (10 : ℝ)⁻¹ by norm_num)
    rw [Real.log_inv] at h
    norm_num at h ⊢
    linarith
  have hlogPos : 0 < Real.log (10 : ℝ) := by linarith
  have hrPos : 0 < r := div_pos (Real.log_pos hratioLo) hlogPos
  have hrSmall : r ≤ 1 / 1000000 := by
    apply (div_le_iff₀ hlogPos).mpr
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < ratio)
    linarith
  have hbasePow : base = (10 : ℝ) ^ (k + 8) := by
    dsimp [base, t]
    rw [pow_add]
    norm_num
    ring
  have hbPos : 0 < (b : ℝ) := hbase.trans hbLo
  have hlogBase : Real.logb 10 base = (k + 8 : ℕ) := by
    rw [hbasePow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 10), mul_one]
  have hlog : Real.logb 10 b = (k + 8 : ℕ) + r := by
    have h := Real.logb_div (b := 10) hbPos.ne' hbase.ne'
    change r = Real.logb 10 b - Real.logb 10 base at h
    rw [hlogBase] at h
    linarith
  have hfloor : ⌊Real.logb 10 b⌋ = ((k + 8 : ℕ) : ℤ) := by
    apply Int.floor_eq_iff.mpr
    rw [hlog]
    push_cast
    constructor <;> linarith
  have hfract : Int.fract (Real.logb 10 b) = r := by
    rw [Int.fract, hfloor, hlog]
    push_cast
    ring
  have hlarge : (1000000 : ℝ) ≤ r⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hrPos).mpr
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000000)).mp hrSmall
    simpa [mul_comm] using h
  have hdigit : (1000000 : ℕ) ≤ digit (Real.logb 10 b) 1 := by
    unfold digit
    simp only [completeQuotient, hfract]
    exact Nat.le_floor (by exact_mod_cast hlarge)
  have hlogHi : Real.log (10000 : ℝ) ≤ 36 := by
    rw [show (10000 : ℝ) = 10 ^ (4 : ℕ) by norm_num, Real.log_pow]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    norm_num at *
    linarith
  refine ⟨0, ?_, by simp [denominatorPair], ?_⟩
  · intro j hj
    have h := Nat.eq_zero_of_le_zero hj
    subst j
    simpa only [completeQuotient, hfract] using hrPos.ne'
  · simp only [denominatorPair, mul_one, Nat.cast_ofNat, Nat.zero_add]
    have hreal : (1000000 : ℝ) ≤ (digit (Real.logb 10 b) 1 : ℝ) := by exact_mod_cast hdigit
    linarith

private abbrev leftIndex (k : ℕ) : ℕ := 100000000 * 10 ^ k
private abbrev rightIndex (k : ℕ) : ℕ := leftIndex k + 10 ^ k

private theorem all_persistent_on_block (k : ℕ) :
    blockCount (persistent 10000) (rightIndex k) =
      blockCount (persistent 10000) (leftIndex k) + 10 ^ k := by
  classical
  change (∑ i ∈ Finset.range (leftIndex k + 10 ^ k),
      if persistent 10000 (i + 2) then 1 else 0) = _
  rw [Finset.sum_range_add]
  congr 1
  calc
    _ = ∑ i ∈ Finset.range ((10 : ℕ) ^ k), (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [if_pos (near_power_persistent k _ (by dsimp [leftIndex]; omega)
        (by dsimp [leftIndex]; omega))]
    _ = _ := by simp

private theorem left_tends : Tendsto leftIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro bound
  filter_upwards [eventually_ge_atTop bound] with k hk
  have hpow := Nat.lt_two_pow_self (n := k)
  have hle := Nat.pow_le_pow_left (show 2 ≤ 10 by decide) k
  have hl := Nat.mul_le_mul_right (10 ^ k) (show 1 ≤ 100000000 by decide)
  simp only [Nat.one_mul] at hl
  exact hk.trans (hpow.le.trans (hle.trans hl))

private theorem right_tends : Tendsto rightIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro bound
  filter_upwards [tendsto_atTop.mp left_tends bound] with k hk
  exact hk.trans (Nat.le_add_right _ _)

private theorem weighted_identity (k : ℕ) :
    (100000001 : ℝ) * (blockCount (persistent 10000) (rightIndex k) : ℝ) / rightIndex k -
      100000000 * (blockCount (persistent 10000) (leftIndex k) : ℝ) / leftIndex k = 1 := by
  have h := all_persistent_on_block k
  have ht : 0 < (10 : ℝ) ^ k := by positivity
  have hR : (rightIndex k : ℝ) = 100000001 * 10 ^ k := by
    simp only [rightIndex, leftIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    ring
  have hL : (leftIndex k : ℝ) = 100000000 * 10 ^ k := by push_cast; rfl
  rw [h, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, hR, hL]
  field_simp
  ring

theorem disproof : ¬ (type_of% @OMA.S_arxiv_2603_18243.main) := by
  intro h
  have htL := h.comp left_tends
  have htR := h.comp right_tends
  have ht := ((tendsto_const_nhds (x := (100000001 : ℝ))).mul htR).sub
    ((tendsto_const_nhds (x := (100000000 : ℝ))).mul htL)
  have hc : (fun k : ℕ =>
      100000001 * ((blockCount (persistent 10000) (rightIndex k) : ℝ) / rightIndex k) -
      100000000 * ((blockCount (persistent 10000) (leftIndex k) : ℝ) / leftIndex k)) =
      fun _ => (1 : ℝ) := by
    funext k
    simpa only [← mul_div_assoc] using weighted_identity k
  change Tendsto (fun k : ℕ =>
    100000001 * ((blockCount (persistent 10000) (rightIndex k) : ℝ) / rightIndex k) -
    100000000 * ((blockCount (persistent 10000) (leftIndex k) : ℝ) / leftIndex k))
    atTop (𝓝 ((100000001 : ℝ) * (1/12) - 100000000 * (1/12))) at ht
  rw [hc] at ht
  have he := tendsto_nhds_unique ht (tendsto_const_nhds (x := (1 : ℝ)))
  norm_num at he

end HymanDensity

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2603_18243.main) := HymanDensity.disproof
