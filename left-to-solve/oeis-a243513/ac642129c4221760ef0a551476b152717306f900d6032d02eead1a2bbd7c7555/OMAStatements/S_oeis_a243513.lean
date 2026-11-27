import Mathlib

/-!
# Generating function and closed form for OEIS A243513

Source: https://oeis.org/A243513

The state records the greatest letter seen and the previous two letters.
Before the first choice, the actual first letter is zero and the state
repeats it once so that no three-letter restriction applies yet. Each
subsequent choice allows an old letter or the next new one, subject to
the consecutive-pattern rule.
-/

namespace OMA.S_oeis_a243513

/-- The largest letter used, the penultimate letter, and the last letter. -/
abbrev WordState := Fin 5 × Fin 5 × Fin 5

def allowed (s : WordState) : List (Fin 5) :=
  ([0, 1, 2, 3, 4] : List (Fin 5)).filter fun z =>
    decide (z.val ≤ s.1.val + 1 ∧ (s.2.1 = s.2.2 ∨ (z ≠ s.2.1 ∧ z ≠ s.2.2)))

def advance (s : WordState) (z : Fin 5) : WordState :=
  (max s.1 z, s.2.2, z)

/-- Suffixes in the literal enumeration of admissible arrays. -/
def suffixes (s : WordState) : ℕ → List (List (Fin 5))
  | 0 => [[]]
  | k + 1 => (allowed s).flatMap fun z => (suffixes (advance s z) k).map (z :: ·)

/-- At (n ≥ 1), count length (n+2) arrays by adding (n+1) letters to the initial zero. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else (suffixes (0, 0, 0) (n + 1)).length

open PowerSeries

theorem main :
    ((1 - X) ^ 2 * (1 - 3 * X) * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (3 - 10 * X + 6 * X ^ 2)) ∧
    (∀ n : ℕ, 1 ≤ n → 4 * a n = 7 + 3 ^ n + 2 * n) := by
  sorry

end OMA.S_oeis_a243513
