import Mathlib

/-!
# A339258: Triangle read by rows T(n,k), (n >= 1, k >= 1), in which row n has length
A000070(n-1) and every column gives A000005, the number of divisors function.

Source: https://oeis.org/A339258
Credit: @esracummings31-blip

Conjecture (Omar E. Pol): the sum of row n equals A006128(n), the total number of parts in all
partitions of n.

Conventions.
* The entry gives T(n,k) = A000005(A176206(n,k)). Row n of A176206 is the nonincreasing list in
  which n-k is repeated A000041(k) times, k = 0..n-1 (as stated in A176206); its length is
  A000070(n-1). So row n of this triangle is the list of d(t) over the terms t of that row.
* A000041(j) is the number of partitions of j; A006128(n) is the total number of parts in all
  partitions of n.
-/

namespace OMA.S_oeis_a339258

/-- A000041: the number of partitions of j. -/
def A000041 (j : ℕ) : ℕ := Fintype.card (Nat.Partition j)

/-- Row n of A176206: n-k repeated A000041(k) times, k = 0..n-1. -/
def rowA176206 (n : ℕ) : List ℕ :=
  (List.range n).flatMap (fun k => List.replicate (A000041 k) (n - k))

/-- Row n of A339258: T(n,k) = A000005(A176206(n,k)). -/
def row (n : ℕ) : List ℕ := (rowA176206 n).map (fun t => (Nat.divisors t).card)

/-- A006128: the total number of parts in all partitions of n. -/
def A006128 (n : ℕ) : ℕ := ∑ p : Nat.Partition n, Multiset.card p.parts

theorem main : ∀ n : ℕ, 1 ≤ n → (row n).sum = A006128 n := by
  sorry

end OMA.S_oeis_a339258
