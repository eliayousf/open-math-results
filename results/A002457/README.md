# Shunia’s square-root formula for OEIS A002457

Joseph M. Shunia conjectured this formula on 11 September 2025. For a positive integer $n$, set $B=16^n$. Then

```math
\left\lfloor\sqrt{(B+1)^{2n+1}}\right\rfloor\bmod B
=\frac{(2n+1)!}{(n!)^2}=(2n+1)\binom{2n}{n}.
```

[OEIS statement](https://oeis.org/A002457/internal)

## Proof

Put $c_j=4^n\binom{n+1/2}{j}$, with the generalized binomial coefficient. The binomial series at $1/B$ gives

```math
\sqrt{(B+1)^{2n+1}}
=4^n B^n(1+1/B)^{n+1/2}
=\sum_{j\ge0}c_jB^{n-j}.
```

For $j\le n$, each $c_j$ is an integer. Indeed, the coefficient of $x^j$ in $(1+4x)^{n+1/2}$ is $4^j\binom{n+1/2}{j}$. The product $(1+4x)^n\sqrt{1+4x}$ has integer coefficients because the coefficient of $x^j$ in its square-root factor is $2(-1)^{j-1}C_{j-1}$ for $j\ge1$, where $C_k=\binom{2k}{k}-\binom{2k}{k+1}$ is the $k$th Catalan number. Multiplying by $4^{n-j}$ gives the claimed integrality. The Lean proof establishes the same integrality by applying Pascal's identity to the half-integer coefficients.

Let $S=\sum_{j=0}^n c_jB^{n-j}$. Starting at $j=n+1$, the terms of the remaining series alternate, beginning with a positive term. The ratio of successive magnitudes is

```math
\frac{j-n-1/2}{B(j+1)}<1.
```

The alternating-series bound puts the remainder between zero and the first omitted term. That term is at most $4^{-n}$ because

```math
\frac{c_{n+1}}{B}
=\frac{4^n}{B}\,\frac{\binom{2n+2}{n+1}}{4^{n+1}}
\le 4^{-n}<1.
```

The integer square root is therefore $S$. Modulo $B$, all terms of $S$ with $j<n$ vanish. Its constant term is $c_n=(2n+1)\binom{2n}{n}$. This is less than $B$ since $\binom{2n}{n}\le4^n$ and $2n+1<4^n$ for $n\ge1$. Thus $c_n$ is the required remainder.

## Verification and attribution

- [Lean proof](../../OpenMath/A002457.lean) uses `Nat.sqrt` for the integer square root and verifies the identity for all positive indices.
- [Exact arithmetic check](check.py) compares the integer square root with the rational truncation and the factorial formula at 123 indices, including $n=256$.
- [Replay instructions](../../README.md#run-the-checks) build the proof, replay the kernel, and audit the theorem's axioms.

Prepared by Elia Yousf with Codex, which found the argument and produced the formalization. A search of the sources checked did not locate an earlier proof of this exact formula. Shunia's earlier work develops related techniques for extracting coefficients from arithmetic expressions. [Related preprint](https://arxiv.org/abs/2404.00332)
