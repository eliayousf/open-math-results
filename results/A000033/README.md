# Van Hoeij's congruence for OEIS A000033

**Lean-checked.** Published by Elia Yousf. Codex found the proof and wrote the Lean formalization. Left to Solve is reviewing the statement. [Statement PR #898](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/898)

## Statement

For the sequence $a(n)$ in OEIS A000033, every positive integer $n$ and prime $p$ satisfy

```math
a(n)+2a(n+p)+a(n+2p)\equiv 0\pmod p.
```

Mark van Hoeij posed this in June 2019. His related A000426 note states a congruence that implies this one, because A000033 at index $n$ is $n$ times A000426 at that index and the three indices agree modulo $p$. The note gives the congruence without a proof reference. Proof priority is unresolved. [Original statement](https://oeis.org/A000033/internal) · [Related note](https://oeis.org/A000426/internal)

## Proof

Let $b(n)=(-1)^n a(n)$. Reindex the published coefficient formula with $r=n-k$ to obtain

```math
b(n)=\sum_{r\ge0}(-1)^r r!\binom{n-r}{2}R_r(n),
\qquad R_r(n)=[x^{2r}](2+x)(1+x)^{n+r-1}.
```

The factor $\frac{2n}{n+r}\binom{n+r}{2r}$ is $\binom{n+r}{2r}+\binom{n+r-1}{2r}$, the coefficient defining $R_r(n)$. That coefficient is zero for $r>n$. Here $\binom{z}{2}=z(z-1)/2$ can also be used when $z<0$. [OEIS coefficient formula](https://oeis.org/A000033)

For odd $p$, the factor $r!$ kills all terms with $r\ge p$ modulo $p$. For each remaining $r$, $\binom{n-r}{2}$ is constant modulo $p$ under a shift of $n$ by $p$. The second difference of $R_r(n)$ with that step is the coefficient of $x^{2r}$ in

```math
(2+x)(1+x)^{n+r-1}\big((1+x)^p-1\big)^2
\equiv (2+x)(1+x)^{n+r-1}x^{2p}\pmod p.
```

The coefficient is zero because $2r<2p$. This proves $b(n+2p)-2b(n+p)+b(n)\equiv0\pmod p$. The signs of $(-1)^n$ at the three indices give the desired congruence for $a$.

For $p=2$ only $r=0,1$ can contribute. The first term is even, while $R_1(n)\equiv n\pmod2$. Thus $a(n)\equiv n\binom{n-1}{2}\pmod2$, which depends only on $n$ modulo four. This gives the required congruence modulo two.

## Verification

- [Lean proof](../../OpenMath/A000033.lean) covers all positive indices and all primes. The replay checks the deduction from the reindexed formula. The identity above connects that formula to the source sequence.
- [Exact Python check](check.py) compares an independent factorial formula with the Lean definition at 600 indices and checks 10,000 instances of the congruence.
- [Replay instructions](../../README.md#run-the-checks) build Lean, audit the theorem's axioms, and run the arithmetic check.
