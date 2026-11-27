# Mathar’s adjacent-sum identity for A005994

Let $a(n)$ be OEIS A005994 and $b(n)$ be OEIS A203286. R. J. Mathar conjectured on 8 March 2025 that $a(n)+a(n+1)=b(n+1)$ for every $n\ge0$. [A005994](https://oeis.org/A005994) · [A203286](https://oeis.org/A203286)

## Proof

An array counted by $b(N)$ has $2N$ nondecreasing entries in $\{-3,\ldots,3\}$, sum zero, and equally many positive and negative entries. Write $p=(p_1,p_2,p_3)$ and $q=(q_1,q_2,q_3)$ for its positive and negative multiplicities by magnitude. Their totals and weighted totals agree, so the two linear equations give $p-q=(d,-2d,d)$ for an integer $d$. Conversely, any such pair whose common total is at most $N$ determines exactly one array by filling the remaining positions with zeros.

Let $e=|d|$. The componentwise minimum of $p$ and $q$ is a triple of nonnegative integers with sum at most $N-2e$. It determines the pair once the sign of $d$ is fixed. By stars and bars there are $\binom{N-2e+3}{3}$ such triples. This gives the count

```math
b(N)=\binom{N+3}{3}+2\sum_{e\ge1}\binom{N-2e+3}{3}.
```

Use the published triangular-number convolution for $a(n)$. It gives $a(n)=\sum_{e\ge0}(2e+1)\binom{n-2e+2}{2}$. Binomial terms in both formulas vanish when their upper index is below the lower one. [A005994 formula](https://oeis.org/A005994)

Set $N=n+1$ and $U(e)=\binom{N-2e+3}{3}$. Applying Pascal’s identity twice yields

```math
\binom{N-2e+1}{2}+\binom{N-2e+2}{2}=U(e)-U(e+1).
```

The adjacent sum is therefore $\sum_{e\ge0}(2e+1)(U(e)-U(e+1))$. The coefficient of $U(0)$ is one and that of every later $U(e)$ is two, which is exactly the formula for $b(N)$.

## Checks and attribution

- The [Lean proof](../../OpenMath/A005994.lean) constructs and counts the multiplicity parametrization and proves the telescoping identity for every index.
- The [exact arithmetic checker](check.py) counts arrays directly through length 10, counts bracelet representatives directly through 12 black beads, and compares independent exact formulas and counts for 200 consecutive indices.

The conjecture is credited to R. J. Mathar. This proof was prepared with Codex. A targeted search of OEIS, arXiv, and public Lean proof catalogues did not find an earlier proof of this exact identity. The separate tentative link to face-magic cubes in A203286 is outside the claim here.
