import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Generating function and closed form for OEIS A243514

Source: https://oeis.org/A243514

The state records the greatest letter seen and the previous two letters.
Before the first choice, the actual first letter is zero and the state
repeats it once so that no three-letter restriction applies yet. Each
subsequent choice allows an old letter or the next new one, subject to
the consecutive-pattern rule.
-/

namespace OMA.S_oeis_a243514

/-- The largest letter used, the penultimate letter, and the last letter. -/
abbrev WordState := Fin 6 × Fin 6 × Fin 6

def allowed (s : WordState) : List (Fin 6) :=
  ([0, 1, 2, 3, 4, 5] : List (Fin 6)).filter fun z =>
    decide (z.val ≤ s.1.val + 1 ∧ (s.2.1 = s.2.2 ∨ (z ≠ s.2.1 ∧ z ≠ s.2.2)))

def advance (s : WordState) (z : Fin 6) : WordState :=
  (max s.1 z, s.2.2, z)

/-- Suffixes in the literal enumeration of admissible arrays. -/
def suffixes (s : WordState) : ℕ → List (List (Fin 6))
  | 0 => [[]]
  | k + 1 => (allowed s).flatMap fun z => (suffixes (advance s z) k).map (z :: ·)

/-- For positive n, add n+1 letters to the initial zero to count length n+2 arrays. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else (suffixes (0, 0, 0) (n + 1)).length

open PowerSeries

theorem main :
    ((1 - X) ^ 2 * (1 - 2 * X) * (1 - 4 * X) * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (3 - 19 * X + 33 * X ^ 2 - 16 * X ^ 3)) ∧
    (∀ n : ℕ, 1 ≤ n → 18 * a n = 26 + 9 * 2 ^ n + 4 ^ n + 6 * n) := by
  sorry

end OMA.S_oeis_a243514
