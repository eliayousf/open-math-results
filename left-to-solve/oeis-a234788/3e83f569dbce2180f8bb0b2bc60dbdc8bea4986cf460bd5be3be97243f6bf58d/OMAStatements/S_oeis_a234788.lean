import Mathlib.NumberTheory.Bernoulli

/-! Common numerator and reduced denominator residues in OEIS A234788.
Source: https://oeis.org/A234788/internal. In the source, Bernoulli degrees are positive and even; the progression starts at 2.
-/

namespace OMA.S_oeis_a234788

/-- The residues where the signed numerator and one sixth of the denominator agree. -/
def commonResidues : Set ℕ :=
  {r | ∃ n : ℕ, 0<n ∧
    ((bernoulli (2*n)).num ≡ (((bernoulli (2*n)).den/6:ℕ):ℤ) [ZMOD 30]) ∧
    r = ((bernoulli (2*n)).den/6)%30}

theorem main :
    (∀ k : ℕ, (bernoulli (20*k+2)).num ≡ (((bernoulli (20*k+2)).den/6 :ℕ):ℤ) [ZMOD 30]) ∧
    commonResidues = ({1,7,11,13,17,19,23,29} : Set ℕ) := by
  sorry

end OMA.S_oeis_a234788
