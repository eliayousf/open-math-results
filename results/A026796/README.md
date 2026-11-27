# Beck’s partition identity with its corrected shift

Let $a(n)$ count partitions of $n$ whose least part is exactly 3, and let $b(n)$ count partitions of $n$ in which twice the number of ones equals the total number of parts. George Beck’s 19 August 2017 comment conjectures $a(n+4)=b(n)$ for every $n\ge0$. [OEIS A026796](https://oeis.org/A026796/internal)

At $n=2$, the only partitions are $(2)$ and $(1,1)$, so $b(2)=0$. The only partition of 6 with least part 3 is $(3,3)$, so $a(6)=1$. This disproves the stated shift with positive indices.

## Corrected identity

For every $n\ge 0$,

```math
a(n+3)=b(n).
```

A balanced partition has as many ones as non-ones. Remove the ones and add 1 to each remaining part. This keeps the sum equal to $n$ and makes every remaining part at least 3. Append one part of size 3 to obtain a partition counted by $a(n+3)$.

Conversely, remove one occurrence of 3 from a partition counted by $a(n+3)$. Subtract 1 from every remaining part and insert one part of size 1 for each subtraction. The remaining parts were at least 3, so each decremented part is at least 2. The result is balanced and sums to $n$. The operations are inverse on multisets, even when several parts equal 3. At $n=0$, the empty balanced partition maps to $(3)$.

## Prior work and verification

- OEIS A008483 records that deleting one part of size 3 converts an A026796 partition of $n+3$ to a partition of $n$ into parts at least 3. Martin Fuller’s proof of a related Beck identity on A008484 groups two ones with each non-one to produce parts at least 4. The proof here uses the one-to-one grouping dictated by A026796. Our search found no earlier direct treatment of the stated shift. [OEIS A008483](https://oeis.org/A008483/internal) · [Fuller’s proof in A008484](https://oeis.org/A008484/internal)
- The [Lean file](../../OpenMath/A026796.lean) uses Mathlib’s `Nat.Partition` with multiset parts. It proves the infinite corrected identity by an explicit equivalence and proves $a(6)=1$ and $b(2)=0$, which refute the original conjecture.
- The [exact Python check](check.py) independently enumerates decreasing partitions. It checks the OEIS prefix, the counterexample, and the bijection in every case from $n=0$ through $36$.
- The written proof, formalization and checker were developed with Codex.
