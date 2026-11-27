import OMAStatements.S_oeis_a008676
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range

/-! Layman's floor formula for partitions into parts 3 and 5, OEIS A008676. -/

namespace OpenMath.A008676

open Finset

/-- Pairs of multiplicities for parts 3 and 5 in a partition of `n`. -/
def representations (n : ℕ) : Finset (ℕ × ℕ) :=
  ((range (n + 1)) ×ˢ (range (n + 1))).filter fun p => 3 * p.1 + 5 * p.2 = n

def a (n : ℕ) : ℕ := (representations n).card

private theorem mem_representations {n : ℕ} {p : ℕ × ℕ} :
    p ∈ representations n ↔ 3 * p.1 + 5 * p.2 = n := by
  simp only [representations, mem_filter, mem_product, mem_range]
  omega

private def shift : (ℕ × ℕ) ↪ (ℕ × ℕ) :=
  ⟨fun p => (p.1 + 5, p.2), by
    intro p q h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    exact Prod.ext (by dsimp at h₁; omega) h₂⟩

-- The inverse of 3 modulo 5 is 2. The first coordinate is the unique
-- representative in [0, 4] that can give a solution at n + 15.
private def extra (n : ℕ) : ℕ × ℕ :=
  let x := (2 * n) % 5
  (x, (n + 15 - 3 * x) / 5)

private theorem small_representation (n : ℕ) (p : ℕ × ℕ) (hp : p.1 < 5) :
    p ∈ representations (n + 15) ↔ p = extra n := by
  obtain ⟨x, y⟩ := p
  change x < 5 at hp
  rw [mem_representations]
  simp only [extra, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨by omega, by omega⟩
  · rintro ⟨rfl, rfl⟩
    omega

private theorem representation_step (n : ℕ) :
    representations (n + 15) = insert (extra n) ((representations n).map shift) := by
  ext p
  rw [mem_insert, mem_map]
  constructor
  · intro h
    by_cases hp : p.1 < 5
    · exact Or.inl ((small_representation n p hp).mp h)
    · have heq := mem_representations.mp h
      refine Or.inr ⟨(p.1 - 5, p.2), mem_representations.mpr ?_, ?_⟩
      · dsimp
        omega
      · apply Prod.ext
        · change p.1 - 5 + 5 = p.1
          exact Nat.sub_add_cancel (by omega)
        · rfl
  · rintro (rfl | ⟨q, hq, rfl⟩)
    · exact (small_representation n (extra n) (Nat.mod_lt _ (by decide))).mpr rfl
    · have heq := mem_representations.mp hq
      apply mem_representations.mpr
      change 3 * (q.1 + 5) + 5 * q.2 = n + 15
      omega

private theorem a_step (n : ℕ) : a (n + 15) = a n + 1 := by
  have h : extra n ∉ (representations n).map shift := by
    intro hmem
    obtain ⟨q, _, heq⟩ := mem_map.mp hmem
    have hx := congrArg Prod.fst heq
    change q.1 + 5 = (2 * n) % 5 at hx
    omega
  unfold a
  rw [representation_step, card_insert_of_notMem h, card_map]

private def floorFormula (n : ℕ) : ℤ :=
  (2 * ((n : ℤ) + 3)) / 3 - (3 * ((n : ℤ) + 3)) / 5

private theorem floor_step (n : ℕ) : floorFormula (n + 15) = floorFormula n + 1 := by
  unfold floorFormula
  rw [show 2 * (((n + 15 : ℕ) : ℤ) + 3) = 2 * ((n : ℤ) + 3) + 10 * 3 by omega,
    show 3 * (((n + 15 : ℕ) : ℤ) + 3) = 3 * ((n : ℤ) + 3) + 9 * 5 by omega,
    Int.add_mul_ediv_right _ _ (by decide), Int.add_mul_ediv_right _ _ (by decide)]
  omega

/-- The floor formula in the 2009 OEIS conjecture, for every index starting at zero. -/
theorem main (n : ℕ) :
    (a n : ℤ) = (2 * ((n : ℤ) + 3)) / 3 - (3 * ((n : ℤ) + 3)) / 5 := by
  change (a n : ℤ) = floorFormula n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 15
    · have base : ∀ i : Fin 15, (a i.val : ℤ) = floorFormula i.val := by decide
      exact base ⟨n, hn⟩
    · have step : (a ((n - 15) + 15) : ℤ) = floorFormula ((n - 15) + 15) := by
        rw [a_step, floor_step]
        have prev := ih (n - 15) (by omega)
        omega
      simpa only [Nat.sub_add_cancel (by omega : 15 ≤ n)] using step

end OpenMath.A008676

theorem OMA.solution : type_of% @OMA.S_oeis_a008676.main := by
  intro n
  exact OpenMath.A008676.main n
