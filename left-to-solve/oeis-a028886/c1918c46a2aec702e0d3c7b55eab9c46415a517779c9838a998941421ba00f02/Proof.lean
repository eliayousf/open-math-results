import OMAStatements.S_oeis_a028886
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Kurkov's prime criterion for numbers of the form `(2m+1)^2-8`, OEIS A028886. -/

namespace OpenMath.A028886

private abbrev Quad := Zsqrtd 2

private theorem two_not_square (n : ℤ) : (2 : ℤ) ≠ n * n := by
  intro h
  have hc : n ≤ -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 ∨ 2 ≤ n := by omega
  rcases hc with hn | rfl | rfl | rfl | hn <;> try norm_num at h
  · nlinarith [mul_nonneg (show 0 ≤ -n - 2 by omega) (show 0 ≤ -n + 2 by omega)]
  · nlinarith [mul_nonneg (show 0 ≤ n - 2 by omega) (show 0 ≤ n + 2 by omega)]

private theorem norm_ne_zero {a : Quad} (ha : a ≠ 0) : a.norm ≠ 0 :=
  fun h => ha ((Zsqrtd.norm_eq_zero two_not_square a).1 h)

private theorem round_bound (a b : ℚ) (hb : b ≠ 0) :
    |a - b * round (a / b)| ≤ |b| / 2 := by
  rw [show a - b * round (a / b) = b * (a / b - round (a / b)) by field_simp,
    abs_mul, div_eq_mul_inv |b|]
  exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using abs_sub_round (a / b))
    (abs_nonneg _)

private def quotient (a b : Quad) : Quad :=
  ⟨round ((a * star b).re / (b.norm : ℚ)), round ((a * star b).im / (b.norm : ℚ))⟩

private theorem remainder_decreases (a : Quad) {b : Quad} (hb : b ≠ 0) :
    (a - b * quotient a b).norm.natAbs < b.norm.natAbs := by
  let r := a - b * quotient a b
  let z := r * star b
  have hB : (b.norm : ℚ) ≠ 0 := by exact_mod_cast norm_ne_zero hb
  have hpos : 0 < |(b.norm : ℚ)| := abs_pos.2 hB
  have hz : z = a * star b - (b.norm : Quad) * quotient a b := by
    dsimp [z, r]
    rw [sub_mul, Zsqrtd.norm_eq_mul_conj]
    ring
  have hr : |(z.re : ℚ)| ≤ |(b.norm : ℚ)| / 2 := by
    rw [hz]
    simpa [Zsqrtd.re_sub, quotient, Zsqrtd.re_mul] using
      round_bound ((a * star b).re : ℚ) (b.norm : ℚ) hB
  have hi : |(z.im : ℚ)| ≤ |(b.norm : ℚ)| / 2 := by
    rw [hz]
    simpa [Zsqrtd.im_sub, quotient, Zsqrtd.im_mul] using
      round_bound ((a * star b).im : ℚ) (b.norm : ℚ) hB
  have hr2 : (z.re : ℚ)^2 ≤ (|(b.norm : ℚ)| / 2)^2 :=
    by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hr
  have hi2 : (z.im : ℚ)^2 ≤ (|(b.norm : ℚ)| / 2)^2 :=
    by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hi
  have hsmall : |(z.norm : ℚ)| < |(b.norm : ℚ)| * |(b.norm : ℚ)| := by
    rw [show (z.norm : ℚ) = (z.re : ℚ)^2 - 2 * (z.im : ℚ)^2 by
      rw [Zsqrtd.norm_def]; push_cast; ring, abs_lt]
    constructor <;> nlinarith
  have hmul : |(r.norm : ℚ)| * |(b.norm : ℚ)| < |(b.norm : ℚ)| * |(b.norm : ℚ)| := by
    simpa [z, Zsqrtd.norm_mul, Zsqrtd.norm_conj, Int.cast_mul, abs_mul] using hsmall
  have hlt := (mul_lt_mul_iff_of_pos_right hpos).1 hmul
  exact_mod_cast (show (r.norm.natAbs : ℚ) < (b.norm.natAbs : ℚ) by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hlt)

private local instance : EuclideanDomain Quad where
  __ := Zsqrtd.commRing
  __ := Zsqrtd.nontrivial
  quotient := quotient
  quotient_zero a := by ext <;> simp [quotient]
  remainder a b := a - b * quotient a b
  quotient_mul_add_remainder_eq a b := by abel
  r a b := a.norm.natAbs < b.norm.natAbs
  r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
  remainder_lt := remainder_decreases
  mul_left_not_lt a b hb := by
    rw [Zsqrtd.norm_mul, Int.natAbs_mul]
    exact not_lt_of_ge (Nat.le_mul_of_pos_right a.norm.natAbs (Int.natAbs_pos.2 (norm_ne_zero hb)))

private theorem norm_dvd {a b : Quad} (h : a ∣ b) : a.norm.natAbs ∣ b.norm.natAbs := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c.norm.natAbs, by rw [Zsqrtd.norm_mul, Int.natAbs_mul]⟩

private theorem nontrivial_factor {s : ℤ} {N : ℕ} (hN : 2 ≤ N)
    (hcop : N.Coprime 2) (hcomp : ¬ N.Prime) (hs : (N : ℤ) = s^2 - 8) :
    ∃ u v : Quad, (⟨s, 2⟩ : Quad) = u * v ∧ ¬ IsUnit u ∧ ¬ IsUnit v := by
  let a : Quad := ⟨s, 2⟩
  have ha : a.norm = (N : ℤ) := by rw [hs, Zsqrtd.norm_def]; dsimp [a]; ring
  have hmul : a * star a = (N : Quad) := by
    rw [← Zsqrtd.norm_eq_mul_conj, ha]
    rfl
  have ha' : ¬ IsUnit a := by
    rw [← Zsqrtd.norm_eq_one_iff, ha, Int.natAbs_natCast]
    omega
  have dvd_cast (d : ℕ) (hd : a ∣ (d : Quad)) : N ∣ d := by
    obtain ⟨w, hw⟩ := hd
    have hw' : (d : Quad) * star a = (N : Quad) * w := by
      calc
        _ = (a * w) * star a := by rw [hw]
        _ = (a * star a) * w := by ring
        _ = _ := by rw [hmul]
    have hcoord := congrArg Zsqrtd.im hw'
    simp [a] at hcoord
    have hint : (N : ℤ) ∣ (d : ℤ) * 2 := ⟨-w.im, by linarith⟩
    have hnat : N ∣ d * 2 := by exact_mod_cast hint
    exact hcop.dvd_mul_right.mp hnat
  have hprime : ¬ Prime a := by
    intro hp
    obtain ⟨d, hd, hd2, hdN⟩ := (Nat.not_prime_iff_exists_dvd_lt hN).1 hcomp
    obtain ⟨e, he⟩ := hd
    have hepos : 0 < e := by
      by_contra! h
      have : e = 0 := by omega
      simp [this] at he
      omega
    have heN : e < N := by
      rw [he]
      nlinarith [mul_nonneg (show 0 ≤ d - 2 by omega) (show 0 ≤ e by omega)]
    have hde : a ∣ (d : Quad) * (e : Quad) := by
      rw [← Nat.cast_mul, ← he, ← hmul]
      exact dvd_mul_right _ _
    rcases hp.dvd_mul.mp hde with h | h
    · exact (not_le_of_gt hdN) (Nat.le_of_dvd (by omega) (dvd_cast d h))
    · exact (not_le_of_gt heN) (Nat.le_of_dvd hepos (dvd_cast e h))
  have hi : ¬ Irreducible a := fun h => hprime (irreducible_iff_prime.mp h)
  simpa [irreducible_iff, ha', not_forall, not_or] using hi

private theorem shared_factor_is_unit {s : ℤ} {N : ℕ} (hs : (N : ℤ) = s^2 - 8)
    (hcop : N.Coprime 2) {b : Quad} (h : b ∣ (⟨s, 2⟩ : Quad))
    (h' : b ∣ (⟨s, -2⟩ : Quad)) : IsUnit b := by
  have ha : (⟨s, 2⟩ : Quad).norm = (N : ℤ) := by rw [hs, Zsqrtd.norm_def]; norm_num; ring
  have hd : b ∣ (⟨0, 4⟩ : Quad) := by
    convert dvd_sub h h' using 1
    ext <;> simp
  have hdN := norm_dvd h
  rw [ha, Int.natAbs_natCast] at hdN
  have hd32 : b.norm.natAbs ∣ 32 := by
    have hnorm : (⟨0, 4⟩ : Quad).norm.natAbs = 32 := by decide
    simpa only [hnorm] using norm_dvd hd
  have hc : N.Coprime 32 := by simpa using hcop.pow_right 5
  have hdiv := Nat.dvd_gcd hdN hd32
  rw [hc.gcd_eq_one] at hdiv
  exact Zsqrtd.norm_eq_one_iff.1 (Nat.dvd_one.mp hdiv)

private def crossed (u v w : Quad) : Prop :=
  (u ∣ w ∧ star v ∣ w) ∨ (star u ∣ w ∧ v ∣ w)

private theorem star_dvd {u w : Quad} (h : u ∣ w) : star u ∣ star w := by
  obtain ⟨q, rfl⟩ := h
  exact ⟨star q, by simp [star_mul, mul_comm]⟩

private theorem crossed_star {u v w : Quad} (h : crossed u v w) : crossed u v (star w) := by
  rcases h with h | h
  · exact Or.inr ⟨star_dvd h.1, by simpa using star_dvd h.2⟩
  · exact Or.inl ⟨by simpa using star_dvd h.1, star_dvd h.2⟩

private theorem crossed_neg {u v w : Quad} (h : crossed u v w) : crossed u v (-w) := by
  simpa [crossed] using h

private theorem crossed_mul {u v w : Quad} (z : Quad) (h : crossed u v w) : crossed u v (w * z) := by
  rcases h with h | h
  · exact Or.inl ⟨dvd_mul_of_dvd_left h.1 _, dvd_mul_of_dvd_left h.2 _⟩
  · exact Or.inr ⟨dvd_mul_of_dvd_left h.1 _, dvd_mul_of_dvd_left h.2 _⟩

private theorem coordinates_nonnegative {u v w : Quad} {N : ℤ}
    (hN : 0 < N) (hw : w.norm = N) (hc : crossed u v w) :
    ∃ x : ℕ, 0 < x ∧ ∃ y : ℤ, 0 ≤ y ∧
      (⟨(x : ℤ), y⟩ : Quad).norm = N ∧ crossed u v ⟨(x : ℤ), y⟩ := by
  let z := if w.re < 0 then -w else w
  have hn : z.norm = N := by dsimp [z]; split <;> simp [hw]
  have hz : crossed u v z := by dsimp [z]; split; exact crossed_neg hc; exact hc
  have hr : 0 ≤ z.re := by
    dsimp [z]
    split
    · change 0 ≤ -w.re
      omega
    · omega
  let t := if z.im < 0 then star z else z
  have ht : t.norm = N := by dsimp [t]; split <;> simp [hn]
  have htc : crossed u v t := by dsimp [t]; split; exact crossed_star hz; exact hz
  have htre : t.re = z.re := by dsimp [t]; split <;> simp
  have htim : 0 ≤ t.im := by
    dsimp [t]
    split
    · change 0 ≤ -z.im
      omega
    · omega
  have hre : t.re ≠ 0 := by
    intro h
    simp only [Zsqrtd.norm_def, h] at ht
    nlinarith [sq_nonneg t.im]
  have hpos : 0 < t.re := lt_of_le_of_ne (htre ▸ hr) (Ne.symm hre)
  have he : (⟨(t.re.natAbs : ℤ), t.im⟩ : Quad) = t := by
    ext
    · exact Int.natAbs_of_nonneg hpos.le
    · rfl
  exact ⟨t.re.natAbs, Int.natAbs_pos.2 hre, t.im, htim, he ▸ ht, he ▸ htc⟩

private theorem reduce_crossed {u v w : Quad} {N : ℤ}
    (hN : 0 < N) (hw : w.norm = N) (hc : crossed u v w) :
    ∃ x y : ℤ, 0 < x ∧ 0 ≤ y ∧ 2 * y ≤ x ∧
      (⟨x, y⟩ : Quad).norm = N ∧ crossed u v ⟨x, y⟩ := by
  classical
  let P (x : ℕ) := 0 < x ∧ ∃ y : ℤ, 0 ≤ y ∧
    (⟨(x : ℤ), y⟩ : Quad).norm = N ∧ crossed u v ⟨(x : ℤ), y⟩
  have hex : ∃ x : ℕ, P x := coordinates_nonnegative hN hw hc
  let x := Nat.find hex
  have hspec : P x := Nat.find_spec hex
  obtain ⟨hx, y, hy, hn, hcross⟩ := hspec
  refine ⟨x, y, by exact_mod_cast hx, hy, ?_, hn, hcross⟩
  by_contra! h
  have hxz : (0 : ℤ) < x := by exact_mod_cast hx
  have hnorm : (x : ℤ)^2 - 2*y^2 = N := by
    simp [Zsqrtd.norm_def] at hn
    linear_combination hn
  have hzpos : 0 < 3 * (x : ℤ) - 4 * y := by
    by_contra! hz
    nlinarith [mul_nonneg (show 0 ≤ 4*y-3*(x : ℤ) by omega)
      (show 0 ≤ 4*y+3*(x : ℤ) by omega), sq_nonneg (x : ℤ)]
  have hzlt : 3 * (x : ℤ) - 4 * y < x := by omega
  let z : Quad := (⟨(x : ℤ), y⟩ : Quad) * ⟨3, -2⟩
  have hznorm : z.norm = N := by
    dsimp [z]
    rw [Zsqrtd.norm_mul, hn, show (⟨3, -2⟩ : Quad).norm = 1 by decide, mul_one]
  have hzcross : crossed u v z := crossed_mul ⟨3, -2⟩ hcross
  have hre : z.re = 3 * (x : ℤ) - 4 * y := by
    dsimp [z]
    ring
  let k : ℕ := z.re.toNat
  have hkcast : (k : ℤ) = z.re := Int.toNat_of_nonneg (hre ▸ hzpos.le)
  have hklt : k < x := by exact_mod_cast (hkcast.trans_lt (hre.trans_lt hzlt))
  apply Nat.find_min hex hklt
  have hkpos : 0 < k := by exact_mod_cast (hkcast.symm ▸ (hre ▸ hzpos))
  refine ⟨hkpos, ?_⟩
  by_cases hem : 0 ≤ z.im
  · have hz : (⟨(k : ℤ), z.im⟩ : Quad) = z := by ext <;> simp [hkcast]
    exact ⟨z.im, hem, hz ▸ hznorm, hz ▸ hzcross⟩
  · have hz : (⟨(k : ℤ), -z.im⟩ : Quad) = star z := by ext <;> simp [hkcast]
    exact ⟨-z.im, by omega, hz ▸ (by simpa using hznorm : (star z).norm = N),
      hz ▸ crossed_star hzcross⟩

private theorem parity_norm {x y s : ℤ} (hs : s % 2 = 1)
    (he : x^2 - 2*y^2 = s^2 - 8) : x % 2 = 1 ∧ y % 2 = 0 := by
  have table : ∀ i j k : ZMod 8, i^2 - 2*j^2 = k^2 → k.val % 2 = 1 →
      i.val % 2 = 1 ∧ j.val % 2 = 0 := by decide
  have h8 : (x : ZMod 8)^2 - 2*(y : ZMod 8)^2 = (s : ZMod 8)^2 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 8)) he
    simpa [Int.cast_sub, Int.cast_mul, Int.cast_pow, show (8 : ZMod 8) = 0 by decide] using h
  have val_mod (z : ℤ) : (↑(z : ZMod 8).val : ℤ) % 2 = z % 2 := by
    rw [ZMod.val_intCast]
    norm_num only [Nat.cast_ofNat]
    rw [Int.emod_emod_of_dvd _ (by decide : (2 : ℤ) ∣ 8)]
  have hs' : (s : ZMod 8).val % 2 = 1 := by
    exact_mod_cast ((val_mod s).trans hs)
  have hval := table (x : ZMod 8) (y : ZMod 8) (s : ZMod 8) h8 hs'
  constructor
  · have h : (↑(x : ZMod 8).val : ℤ) % 2 = 1 := by exact_mod_cast hval.1
    rwa [val_mod] at h
  · have h : (↑(y : ZMod 8).val : ℤ) % 2 = 0 := by exact_mod_cast hval.2
    rwa [val_mod] at h

private theorem extra_representation {s : ℤ} {N : ℕ}
    (hN : 2 ≤ N) (hs : (N : ℤ) = s^2-8) (hs7 : 7 ≤ s) (hodd : s % 2 = 1)
    (hcop : N.Coprime 2) (hcomp : ¬N.Prime) :
    ∃ x y : ℤ, s < x ∧ x ≤ 3*s-10 ∧ x % 2 = 1 ∧ 0 ≤ y ∧ y % 2 = 0 ∧
      x^2-2*y^2 = s^2-8 := by
  obtain ⟨u, v, he, hu, hv⟩ := nontrivial_factor hN hcop hcomp hs
  have huz : u ∣ (⟨s, 2⟩ : Quad) := ⟨v, he⟩
  have hvz : v ∣ (⟨s, 2⟩ : Quad) := ⟨u, he.trans (mul_comm _ _)⟩
  have hpos : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw : (u * star v).norm = (N : ℤ) := by
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj, ← Zsqrtd.norm_mul, ← he,
      hs, Zsqrtd.norm_def]
    norm_num
    ring
  have hw' : crossed u v (u * star v) := Or.inl ⟨dvd_mul_right _ _, dvd_mul_left _ _⟩
  obtain ⟨x, y, hx, hy, hbal, hnorm, hcross⟩ := reduce_crossed hpos hw hw'
  have hxy : x^2-2*y^2 = s^2-8 := by
    simp [Zsqrtd.norm_def, hs] at hnorm
    linear_combination hnorm
  obtain ⟨hpx, hpy⟩ := parity_norm hodd hxy
  have hy2 : 2 ≤ y := by
    by_contra! hy'
    have he0 : y = 0 := by omega
    have hxs : x < s := by
      by_contra! h
      nlinarith [mul_nonneg (show 0 ≤ x-s by omega) (show 0 ≤ x+s by omega)]
    have hx' : x ≤ s-1 := by omega
    nlinarith [mul_nonneg (show 0 ≤ s-1-x by omega) (show 0 ≤ s-1+x by omega)]
  have hge : s ≤ x := by
    by_contra! h
    nlinarith [mul_pos (show 0 < s-x by omega) (show 0 < s+x by omega),
      mul_nonneg (show 0 ≤ y-2 by omega) (show 0 ≤ y+2 by omega)]
  have hne : x ≠ s := by
    intro h
    have hyeq : y = 2 := by
      have hp : (y-2)*(y+2) = 0 := by rw [h] at hxy; nlinarith
      rcases mul_eq_zero.mp hp with h₁ | h₂ <;> omega
    subst x
    subst y
    rcases hcross with hz | hz
    · exact hv (isUnit_star.mp (shared_factor_is_unit hs hcop hz.2 (star_dvd hvz)))
    · exact hu (isUnit_star.mp (shared_factor_is_unit hs hcop hz.1 (star_dvd huz)))
  have hle : x ≤ 3*s-10 := by
    by_contra! h
    nlinarith [mul_nonneg (show 0 ≤ x-2*y by omega) (show 0 ≤ x+2*y by omega),
      mul_pos (show 0 < x-(3*s-10) by omega) (show 0 < x+(3*s-10) by omega), sq_nonneg (s-7)]
  exact ⟨x, y, lt_of_le_of_ne hge (Ne.symm hne), hle, hpx, hy, hpy, hxy⟩

private theorem prime_no_representation {s : ℤ} {N : ℕ} (hs : (N : ℤ) = s^2-8)
    (hs7 : 7 ≤ s) (hp : N.Prime) {x r : ℤ}
    (hx : s < x) (hx' : x ≤ 3*s-10) (hr : 0 ≤ r) (he : x^2-8*r^2 = s^2-8) : False := by
  have hsq : x^2 ≤ (3*s-10)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 3*s-10-x by omega) (show 0 ≤ 3*s-10+x by omega)]
  have hr' : r ≤ s-4 := by
    by_contra! h
    nlinarith [mul_nonneg (show 0 ≤ r-(s-3) by omega) (show 0 ≤ r+(s-3) by omega)]
  have hbound : x+s*r < N := by
    nlinarith only [hx', hs,
      mul_nonneg (show 0 ≤ s by omega) (show 0 ≤ s-4-r by omega), hs7]
  have hpos : 0 < x+s*r := by
    nlinarith only [mul_nonneg (show 0 ≤ s by omega) hr, hx, hs7]
  have hdiv : (N : ℤ) ∣ (x-s*r)*(x+s*r) := by
    refine ⟨1-r^2, ?_⟩
    rw [hs]
    linear_combination he
  have hd : N ∣ (x-s*r).natAbs * (x+s*r).natAbs := by
    rw [← Int.natAbs_mul, ← Int.natCast_dvd_natCast, Int.dvd_natAbs]
    exact hdiv
  have hna : (x-s*r).natAbs < N := by
    have hlt : |x-s*r| < (N : ℤ) := by
      rw [abs_lt]
      constructor <;> nlinarith only [hbound, mul_nonneg (show 0 ≤ s by omega) hr, hx, hs7]
    exact_mod_cast (show ((x-s*r).natAbs : ℤ) < (N : ℤ) by simpa using hlt)
  have hnb : (x+s*r).natAbs < N := by
    exact_mod_cast (show ((x+s*r).natAbs : ℤ) < (N : ℤ) by
      rwa [Int.natAbs_of_nonneg hpos.le])
  rcases hp.dvd_mul.mp hd with hd | hd
  · have h0 : (x-s*r).natAbs = 0 := by
      by_contra hn
      exact (not_le_of_gt hna) (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
    have hx0 : x = s*r := by have := Int.natAbs_eq_zero.mp h0; omega
    have hf : (s^2-8)*(r^2-1) = 0 := by rw [hx0] at he; linear_combination he
    have hr1 : r = 1 := by
      have hn : s^2-8 ≠ 0 := by
        have hp' : (0 : ℤ) < N := by exact_mod_cast hp.pos
        rw [← hs]; exact hp'.ne'
      have he' := (mul_eq_zero.mp hf).resolve_left hn
      have hfactor : (r-1)*(r+1) = 0 := by linear_combination he'
      rcases mul_eq_zero.mp hfactor with h₁ | h₂ <;> omega
    rw [hr1, mul_one] at hx0
    omega
  · exact (not_le_of_gt hnb) (Nat.le_of_dvd (Int.natAbs_pos.2 hpos.ne') hd)

private theorem choose_two_scaled (m q : ℕ) :
    2 * ((q*(m+1) + q.choose 2 + 1 : ℕ) : ℤ) = (q : ℤ)*((q : ℤ)+2*m+1)+2 := by
  cases q with
  | zero => simp
  | succ q =>
    have hpair : (2 : ℕ) ∣ (q+1)*q := by
      simpa [mul_comm] using (even_iff_two_dvd.mp (Nat.even_mul_succ_self q))
    have hbin : 2 * (q+1).choose 2 = (q+1)*q := by
      rw [Nat.choose_two_right, Nat.add_sub_cancel]
      rw [mul_comm, Nat.div_mul_cancel hpair]
    have h : (2 : ℤ) * ((q+1).choose 2 : ℤ) = ((q:ℤ)+1)*q := by exact_mod_cast hbin
    push_cast
    linear_combination h

/-- Kurkov's OEIS criterion for primality of odd squares minus eight. -/
theorem main (m : ℕ) (hm : 2 < m) :
    ((2*m+1)^2-8).Prime ↔ ∀ q : ℕ, 1 ≤ q → q ≤ 2*(m-2) →
      ¬IsSquare (q*(m+1) + q.choose 2 + 1) := by
  let s : ℤ := 2*(m : ℤ)+1
  let N : ℕ := (2*m+1)^2-8
  have hmz : (2 : ℤ) < m := by exact_mod_cast hm
  have hs7 : 7 ≤ s := by dsimp [s]; omega
  have hs : (N : ℤ) = s^2-8 := by
    have h : 8 ≤ (2*m+1)^2 := by
      have h7 : 7 ≤ 2*m+1 := by omega
      exact (by decide : 8 ≤ (7 : ℕ)^2).trans (Nat.pow_le_pow_left h7 2)
    dsimp [N, s]
    rw [Int.ofNat_sub h]
    push_cast
    ring
  have hN : 2 ≤ N := by
    have h : (2 : ℤ) ≤ N := by nlinarith [sq_nonneg (s-7)]
    exact_mod_cast h
  have hodd : s % 2 = 1 := by dsimp [s]; omega
  have hcop : N.Coprime 2 := by
    have h : ((N : ℤ) % 2) = 1 := by
      rw [hs, Int.sub_emod, pow_two, Int.mul_emod, hodd]
      decide
    have h' : N % 2 = 1 := by exact_mod_cast h
    exact Nat.coprime_two_right.mpr (Nat.odd_iff.mpr h')
  have hbound (q : ℕ) : q ≤ 2*(m-2) ↔ (s+2*(q : ℤ) : ℤ) ≤ 3*s-10 := by
    dsimp [s]
    omega
  change N.Prime ↔ _
  constructor
  · intro hp q hq hq' hsq
    obtain ⟨r, hr⟩ := (isSquare_iff_exists_sq _).mp hsq
    have hrc : ((q*(m+1) + q.choose 2 + 1 : ℕ) : ℤ) = (r : ℤ)^2 := by exact_mod_cast hr
    have hchoose := choose_two_scaled m q
    have he : (s+2*(q : ℤ))^2-8*(r : ℤ)^2 = s^2-8 := by
      dsimp [s]
      rw [hrc] at hchoose
      linear_combination -4*hchoose
    exact prime_no_representation hs hs7 hp (by omega) ((hbound q).1 hq') (by positivity) he
  · intro h
    by_contra hcomp
    obtain ⟨x, y, hx, hx', hpx, hy, hpy, hxy⟩ :=
      extra_representation hN hs hs7 hodd hcop hcomp
    let q := ((x-s)/2).toNat
    let r := (y/2).toNat
    have hqcast : (q : ℤ) = (x-s)/2 := Int.toNat_of_nonneg (by omega)
    have hrcast : (r : ℤ) = y/2 := Int.toNat_of_nonneg (by omega)
    have hxs : x = s+2*(q : ℤ) := by omega
    have hyr : y = 2*(r : ℤ) := by omega
    have hq : 1 ≤ q := by omega
    have hq' := (hbound q).2 (hxs ▸ hx')
    have hchoose := choose_two_scaled m q
    have hsq : ((q*(m+1)+q.choose 2+1 : ℕ) : ℤ) = (r : ℤ)^2 := by
      rw [hxs, hyr] at hxy
      dsimp [s] at hxy
      nlinarith only [hchoose, hxy]
    apply h q hq hq'
    apply (isSquare_iff_exists_sq _).mpr
    exact ⟨r, by exact_mod_cast hsq⟩

end OpenMath.A028886

theorem OMA.solution : type_of% @OMA.S_oeis_a028886.main := OpenMath.A028886.main
