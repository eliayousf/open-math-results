import Mathlib.RingTheory.PowerSeries.Basic

/-!
# OEIS A321225: decimal chunks of the periodic word 12321

Source: https://oeis.org/A321225
The first chunk has index one, and the generating series has zero constant
coefficient. A cut occurs when the sum in the prefix reaches a triangular number.
-/

namespace OMA.S_oeis_a321225

def digit (i : ℕ) : ℕ :=
  if i % 5 = 2 then 3 else if i % 5 = 1 ∨ i % 5 = 3 then 2 else 1

def prefixSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => prefixSum n + digit n

def triangle (n : ℕ) : ℕ := n * (n+1) / 2

noncomputable def cut (n : ℕ) : ℕ :=
  sInf {k : ℕ | prefixSum k = triangle n}

def decimal (start : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => 10 * decimal start k + (digit (start+k) : ℤ)

noncomputable def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => decimal (cut n) (cut (n+1) - cut n)

theorem main :
    (∀ n : ℕ, 18 < n → a n = 100001*a (n-9) - 100000*a (n-18)) ∧
    (let x := (PowerSeries.X : PowerSeries ℤ)
     (100000*x^18 - 100001*x^9 + 1) * PowerSeries.mk a =
      x*(10000*x^16 + 20000*x^15 + 30000*x^14 + 21100*x^13 + 23000*x^12
        + 21120*x^11 + 32110*x^10 + 23210*x^9 + 12321*x^8 + 2321*x^7
        + 3211*x^6 + 2112*x^5 + 23*x^4 + 211*x^3 + 3*x^2 + 2*x + 1)) := by
  sorry

end OMA.S_oeis_a321225
