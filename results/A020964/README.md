# Wu’s recurrence for the silver-ratio floor sum

Let $\alpha=1+\sqrt2$ and let $a(n)=\sum_{k\ge1}\lfloor3\alpha^{n-k}\rfloor$ for $n\ge0$. Chai Wah Wu conjectured the recurrence below and its generating function on 14 September 2026. [OEIS A020964](https://oeis.org/A020964/internal)

```math
a(n)=3a(n-1)-4a(n-3)+a(n-4)+a(n-5)\qquad(n>6).
```

## Proof

The exponent $-1$ contributes one because $1<3/\alpha<2$. All exponents at most $-2$ contribute zero because $0<3/\alpha^2<1$ and $\alpha>1$. Consequently $a(n)=1+\sum_{j=0}^{n-1}f(j)$, where $f(j)=\lfloor3\alpha^j\rfloor$. In particular $a(n+1)-a(n)=f(n)$.

Put $\beta=1-\sqrt2$ and $u_j=\alpha^j+\beta^j$. Both bases satisfy $t^2=2t+1$. Hence $u_{j+2}=2u_{j+1}+u_j$, and $u_0=u_1=2$ show that each $u_j$ is integral. For $j\ge2$, we have $|3\beta^j|<1$ because $-1/2<\beta<0$. Since $3\alpha^j=3u_j-3\beta^j$, the sign of $\beta^j$ determines the floor.

```math
f(j)=3u_j-\begin{cases}1&j\text{ even},\\0&j\text{ odd}.\end{cases}
```

Let $E$ shift a sequence forward by one index. The trace recurrence is annihilated by $E^2-2E-1$ and the correction has period two. Thus $(E^2-2E-1)(E^2-1)f=0$ at every index $j\ge2$. Applying this identity to $(E-1)a=f$ gives

```math
a(j+5)-3a(j+4)+4a(j+2)-a(j+1)-a(j)=0\qquad(j\ge2).
```

Setting $n=j+5$ proves the stated recurrence.

The same floor formula gives $a(0),\ldots,a(6)=1,4,11,28,70,171,417$, using $f(0)=3$ and $f(1)=7$. Put $A(x)=\sum_{n\ge0}a(n)x^n$. Multiplying by $1-3x+4x^3-x^4-x^5$ makes every coefficient above degree six vanish. The seven initial values give the remaining coefficients, so

```math
A(x)=\frac{1+x-x^2-x^3+x^4+x^6}{1-3x+4x^3-x^4-x^5}.
```

The denominator is $-(x-1)^2(x+1)(x^2+2x-1)$, which gives Wu’s published form.

## Verification and provenance

- The [Lean file](../../OpenMath/A020964.lean) proves the recurrence at every stated index, identifies the finite sum with the original infinite sum, and proves the normalized generating function over integer formal power series.
- The [arithmetic checker](check.py) instead builds the powers as $c_j+d_j\sqrt2$ with integer coefficients and computes each floor as $3c_j+\operatorname{isqrt}(18d_j^2)$. It tests the recurrence and the generating-function coefficients through index 1000.
- The recurrence and generating-function conjectures are credited to Chai Wah Wu. The source credits the floor-sum sequence to Clark Kimberling. A targeted search for the exact pair of formulas found the OEIS conjecture and related floor sums. Proof priority is unclaimed. [OEIS source](https://oeis.org/A020964/internal)
