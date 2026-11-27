import OMAStatements.S_oeis_a275667
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace OpenMath.A275667

open OMA.S_oeis_a275667

noncomputable section

private def doubling : Point →+ Point where
  toFun p := (2 * p.1, 2 * p.2)
  map_zero' := by decide
  map_add' p q := by ext <;> simp [mul_add]

private theorem doubling_injective : Function.Injective doubling := by
  intro p q h
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    change 2 * p.1 = 2 * q.1 at hx
    omega
  · have hy := congrArg Prod.snd h
    change 2 * p.2 = 2 * q.2 at hy
    omega

private def dilate : Config →+* Config :=
  AddMonoidAlgebra.mapDomainRingHom (ZMod 2) doubling

private theorem dilate_eq_square (p : Config) : dilate p = p ^ 2 := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | single p c =>
    have hc : c * c = c := by
      have h0 : (0 : ZMod 2) * 0 = 0 := zero_mul _
      have h1 : (1 : ZMod 2) * 1 = 1 := one_mul _
      fin_cases c <;> first | exact h0 | exact h1
    rw [pow_two, AddMonoidAlgebra.single_mul_single, hc]
    change AddMonoidAlgebra.mapDomain doubling (AddMonoidAlgebra.single p c) = _
    rw [AddMonoidAlgebra.mapDomain_single]
    congr 1
    ext <;> simp [doubling, two_mul]
  | add p q hp hq =>
    have h₂ : (2 : Config) = 0 := by
      let i : ZMod 2 →+* Config := AddMonoidAlgebra.singleZeroRingHom
      calc
        (2 : Config) = i 2 := (map_ofNat i 2).symm
        _ = i 0 := congrArg i (show (2 : ZMod 2) = 0 by decide)
        _ = 0 := map_zero i
    rw [map_add, hp, hq]
    calc
      p ^ 2 + q ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q := by simp [h₂]
      _ = (p + q) ^ 2 := by ring

private theorem support_dilate (p : Config) :
    (dilate p).coeff.support = p.coeff.support.image doubling :=
  Finsupp.mapDomain_support_of_injective doubling_injective p.coeff

private theorem support_shift_dilate (p : Config) (v : Point) :
    (monomial v * dilate p).coeff.support = (p.coeff.support.image doubling).image (v + ·) := by
  rw [monomial, AddMonoidAlgebra.support_coeff_single_mul_eq_image _ (fun _ => by rw [one_mul]) (.all v),
    support_dilate]

private theorem shift_dilate_card (p : Config) (v : Point) :
    (monomial v * dilate p).coeff.support.card = p.coeff.support.card := by
  rw [support_shift_dilate, Finset.card_image_of_injective _ (add_right_injective v),
    Finset.card_image_of_injective _ doubling_injective]

private theorem disjoint_shift_dilate (p : Config) (v w : Point)
    (h : (v.1 % 2, v.2 % 2) ≠ (w.1 % 2, w.2 % 2)) :
    Disjoint (monomial v * dilate p).coeff.support (monomial w * dilate p).coeff.support := by
  rw [support_shift_dilate, support_shift_dilate, Finset.disjoint_left]
  intro r hr hs
  rcases Finset.mem_image.mp hr with ⟨a, ha, rfl⟩
  rcases Finset.mem_image.mp hs with ⟨b, hb, hab⟩
  rcases Finset.mem_image.mp ha with ⟨x, _, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨y, _, rfl⟩
  apply h
  have hx := congrArg Prod.fst hab
  have hy := congrArg Prod.snd hab
  change w.1 + 2 * y.1 = v.1 + 2 * x.1 at hx
  change w.2 + 2 * y.2 = v.2 + 2 * x.2 at hy
  exact Prod.ext (by omega) (by omega)

private theorem stencil_square_card (p : Config) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    (stencil s * p ^ 2).coeff.support.card = 3 * p.coeff.support.card := by
  rw [← dilate_eq_square, stencil, add_mul, add_mul]
  have h01 : ((0 : ℤ) % 2, (0 : ℤ) % 2) ≠ (s % 2, 0 % 2) := by
    rcases hs with rfl | rfl <;> decide
  have h02 : ((0 : ℤ) % 2, (0 : ℤ) % 2) ≠ (0 % 2, s % 2) := by
    rcases hs with rfl | rfl <;> decide
  have h12 : (s % 2, (0 : ℤ) % 2) ≠ (0 % 2, s % 2) := by
    rcases hs with rfl | rfl <;> decide
  have d01 := disjoint_shift_dilate p (0, 0) (s, 0) h01
  have d02 := disjoint_shift_dilate p (0, 0) (0, s) h02
  have d12 := disjoint_shift_dilate p (s, 0) (0, s) h12
  simp only [AddMonoidAlgebra.coeff_add]
  have dUnion := Finset.disjoint_union_left.mpr ⟨d02, d12⟩
  have hFirst := Finsupp.support_add_eq d01
  have dLast : Disjoint
      ((monomial (0, 0) * dilate p).coeff + (monomial (s, 0) * dilate p).coeff).support
      (monomial (0, s) * dilate p).coeff.support := hFirst.symm ▸ dUnion
  rw [Finsupp.support_add_eq dLast, hFirst, Finset.card_union_of_disjoint dUnion,
    Finset.card_union_of_disjoint d01, shift_dilate_card, shift_dilate_card, shift_dilate_card]
  omega

private def stepPair : Config := stencil 1 * stencil (-1)

private theorem generation_even (n : ℕ) : generation (2 * n) = stepPair ^ n := by
  induction n with
  | zero => simp [generation]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    rw [generation, generation, if_neg (by omega), if_pos (by omega), ih, pow_succ]
    unfold stepPair
    ring

private theorem generation_odd (n : ℕ) :
    generation (2 * n + 1) = stencil 1 * stepPair ^ n := by
  rw [generation, if_pos (by omega), generation_even]

theorem recurrence : population 0 = 1 ∧ ∀ n : ℕ, population (2 * n + 1) = 3 * population n := by
  constructor
  · simp [population, generation]
  intro n
  rcases (show ∃ k, n = 2 * k ∨ n = 2 * k + 1 from ⟨n / 2, by omega⟩) with
    ⟨k, rfl | rfl⟩
  · have hshape : generation (2 * (2 * k) + 1) = stencil 1 * generation (2 * k) ^ 2 := by
      rw [generation_odd, generation_even, show 2 * k = k * 2 by omega, pow_mul]
    simpa only [population, hshape] using stencil_square_card (generation (2 * k)) 1 (Or.inl rfl)
  · have hshape : generation (2 * (2 * k + 1) + 1) = stencil (-1) * generation (2 * k + 1) ^ 2 := by
      rw [generation_odd (2 * k + 1), generation_odd k, pow_succ,
        show 2 * k = k * 2 by omega, pow_mul, mul_pow]
      unfold stepPair
      ring
    simpa only [population, hshape] using stencil_square_card (generation (2 * k + 1)) (-1) (Or.inr rfl)

end
end OpenMath.A275667

theorem OMA.solution : type_of% @OMA.S_oeis_a275667.main :=
  OpenMath.A275667.recurrence
