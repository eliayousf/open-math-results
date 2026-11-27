import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Generating function and closed form for OEIS A243515

Source: https://oeis.org/A243515

The state records the greatest letter seen and the previous two letters.
Before the first choice, the actual first letter is zero and the state
repeats it once so that no three-letter restriction applies yet. Each
subsequent choice allows an old letter or the next new one, subject to
the consecutive-pattern rule.
-/

namespace OMA.S_oeis_a243515

/-- The largest letter used, the penultimate letter, and the last letter. -/
abbrev WordState := Fin 7 × Fin 7 × Fin 7

def allowed (s : WordState) : List (Fin 7) :=
  ([0, 1, 2, 3, 4, 5, 6] : List (Fin 7)).filter fun z =>
    decide (z.val ≤ s.1.val + 1 ∧ (s.2.1 = s.2.2 ∨ (z ≠ s.2.1 ∧ z ≠ s.2.2)))

def advance (s : WordState) (z : Fin 7) : WordState :=
  (max s.1 z, s.2.2, z)

/-- Suffixes in the literal enumeration of admissible arrays. -/
def suffixes (s : WordState) : ℕ → List (List (Fin 7))
  | 0 => [[]]
  | k + 1 => (allowed s).flatMap fun z => (suffixes (advance s z) k).map (z :: ·)

/-- For positive n, add n+1 letters to the initial zero to count length n+2 arrays. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else (suffixes (0, 0, 0) (n + 1)).length

open PowerSeries

theorem main :
    ((1 - X) ^ 2 * (1 - 2 * X) * (1 - 3 * X) * (1 - 5 * X) * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (3 - 31 * X + 106 * X ^ 2 - 141 * X ^ 3 + 60 * X ^ 4)) ∧
    (∀ n : ℕ, 1 ≤ n → 96 * a n = 147 + 2 ^ (5 + n) + 4 * 3 ^ (1 + n) + 5 ^ n + 36 * n) := by
  sorry

end OMA.S_oeis_a243515
