# An endpoint correction to Bos’s A003477 identity

Arie Bos proposed that $a(n)=b(n)+2\sum_{j=1}^{n-3}a(j)$, where $a$ is A003477 and $b$ is A077854. Both entries start at index zero. At $n=4$, the left side is $33$ and the right side is $25+2\cdot3=31$, so the equality fails even for a nonempty sum. [OEIS A003477](https://oeis.org/A003477/internal) · [OEIS A077854](https://oeis.org/A077854/internal)

Including $a(0)$ gives the corrected equality.

```math
a(n)=b(n)+2\sum_{j=0}^{n-3}a(j) \qquad (n\ge3).
```

## Proof

Set $D=(1-2x)(1+x^2)$, $P=1-x-2x^3$, and $Q=1-x$. The source generating functions are $A=(DP)^{-1}$ and $B=(DQ)^{-1}$. All factors have constant coefficient one, so these are identities in the ring of formal power series over the integers. Subtracting and using $Q-P=2x^3$ gives

```math
A-B=\frac{Q-P}{DPQ}=2x^3A\,(1-x)^{-1}.
```

The coefficient of $x^n$ on the right is $2sum_{j=0}^{n-3}a(j)$. This proves the corrected equality. Since $a(0)=1$, the expression in Bos’s conjecture is exactly two less than $a(n)$ throughout its nonempty-sum range.

## Verification and provenance

- The [Lean proof](../../OpenMath/A003477.lean) defines both sequences from the source generating functions. It checks the corrected equality for every $nge3$ and refutes the printed statement on $nge4$.
- The [Python check](check.py) independently generates coefficients of the defining factors using finite binomial sums and convolution. It reproduces the OEIS initial terms and checks the corrected equality and the discrepancy through index 300.
- Targeted searches through OEIS, the web, and trureturing on 27 November 2026 did not identify an earlier presentation of this specific endpoint correction. The generating function calculation is elementary, and this write-up makes no first-proof claim.
