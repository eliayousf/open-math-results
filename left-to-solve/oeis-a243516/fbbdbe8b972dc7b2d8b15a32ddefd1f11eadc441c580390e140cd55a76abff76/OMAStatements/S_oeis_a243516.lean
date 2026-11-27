import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Generating function and closed form for OEIS A243516

Source: https://oeis.org/A243516

The state records the greatest letter seen and the previous two letters.
Before the first choice, the actual first letter is zero and the state
repeats it once so that no three-letter restriction applies yet. Each
subsequent choice allows an old letter or the next new one, subject to
the consecutive-pattern rule.
-/

namespace OMA.S_oeis_a243516

/-- The largest letter used, the penultimate letter, and the last letter. -/
abbrev WordState := Fin 8 × Fin 8 × Fin 8

def allowed (s : WordState) : List (Fin 8) :=
  ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 8)).filter fun z =>
    decide (z.val ≤ s.1.val + 1 ∧ (s.2.1 = s.2.2 ∨ (z ≠ s.2.1 ∧ z ≠ s.2.2)))

def advance (s : WordState) (z : Fin 8) : WordState :=
  (max s.1 z, s.2.2, z)

/-- Suffixes in the literal enumeration of admissible arrays. -/
def suffixes (s : WordState) : ℕ → List (List (Fin 8))
  | 0 => [[]]
  | k + 1 => (allowed s).flatMap fun z => (suffixes (advance s z) k).map (z :: ·)

/-- For positive n, add n+1 letters to the initial zero to count length n+2 arrays. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else (suffixes (0, 0, 0) (n + 1)).length

open PowerSeries

theorem main :
    ((1 - X) ^ 2 * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X) * (1 - 6 * X) * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (3 - 46 * X + 258 * X ^ 2 - 655 * X ^ 3 + 739 * X ^ 4 - 288 * X ^ 5)) ∧
    (∀ n : ℕ, 1 ≤ n → 1800 * a n = 2722 + 675 * 2 ^ n + 25 * 2 ^ (1 + 2 * n) +
      50 * 3 ^ (1 + n) + 2 ^ n * 3 ^ (1 + n) + 660 * n) := by
  sorry

end OMA.S_oeis_a243516
