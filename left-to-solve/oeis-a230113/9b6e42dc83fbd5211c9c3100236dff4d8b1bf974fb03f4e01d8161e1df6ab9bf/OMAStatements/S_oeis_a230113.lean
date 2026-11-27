import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Generating function and recurrence of OEIS A230113

Source: https://oeis.org/A230113
The Lucas offset follows the OEIS examples, which use the digital
root of L(0)=2 in the first term and of L(6)=18 in the second term.
The index is 1-based, with coefficient at zero adjoined.
-/

namespace OMA.S_oeis_a230113

open PowerSeries

/-- Two consecutive terms of the recursion x(n+2)=x(n+1)+x(n). -/
def consecutive (u v : ℕ) : ℕ → ℕ × ℕ
  | 0 => (u, v)
  | n + 1 =>
    let (x, y) := consecutive u v n
    (y, x + y)

def fib (n : ℕ) : ℕ := (consecutive 0 1 n).1
def lucas (n : ℕ) : ℕ := (consecutive 2 1 n).1

-- The residues prime to 30, in increasing order.
def residue (j : Fin 8) : ℕ := ![1, 7, 11, 13, 17, 19, 23, 29] j

/-- The zero-based enumeration of the positive integers prime to 30. -/
def input (n : ℕ) : ℕ := 30 * (n / 8) + residue ⟨n % 8, Nat.mod_lt _ (by decide)⟩

/-- The decimal digital root, also defined at zero. -/
def root (k : ℕ) : ℕ := if k = 0 then 0 else if k % 9 = 0 then 9 else k % 9

/-- The Lucas data in the source example use the first listed term L(0),
while the Fibonacci data begin with F(1). -/
def term (n : ℕ) : ℤ := root (root (fib (input n)) + root (lucas (input n - 1)))

/-- The published sequence is indexed from 1. Adjoin the zero coefficient. -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => term n

theorem main :
    (∀ n : ℕ, 17 < n → a n = a (n-1) - a (n-16) + a (n-17)) ∧
    (((1-X : ℤ⟦X⟧) * (1+X^16)) * mk a =
      C 3 * X^1 + X^2 + X^3 + X^4 - X^6 - X^7 - X^8 + X^9 + C 2 * X^10 -
        X^12 - X^13 - X^14 + C 2 * X^16 + C 4 * X^17) := by
  sorry

end OMA.S_oeis_a230113
