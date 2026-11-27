# Layman’s floor formula for partitions into threes and fives

Let $a(n)$ count the pairs $(x,y)$ of nonnegative integers with $3x+5y=n$. Each pair is a partition using only parts $3$ and $5$, and the generating function is $1/((1-z^3)(1-z^5))$. John W. Layman conjectured the following identity on 23 September 2009. [OEIS A008676](https://oeis.org/A008676/internal)

```math
a(n)=left\lfloor\frac{2(n+3)}{3}\right\rfloor-left\lfloor\frac{3(n+3)}{5}\right\rfloor
\qquad(n\ge 0).
```

## Proof

The map $(x,y)\mapsto(x+5,y)$ bijects solutions at $n$ with solutions at $n+15$ whose first coordinate is at least $5$. Among the remaining possibilities $0\le x<5$, exactly one satisfies $3x\equiv n+15\pmod 5$, namely $x\equiv 2n\pmod 5$. For this $x$, the integer $y=(n+15-3x)/5$ is nonnegative because $3x\le 12$. Hence $a(n+15)=a(n)+1$.

The two floor terms increase by $10$ and $9$, respectively, when the input increases by $15$. Their difference also increases by one. Direct evaluation at $n=0,\ldots,14$ gives the same values for both sides.

```text
1 0 0 1 0 1 1 0 1 1 1 1 1 1 1
```

The step of $15$ extends the equality to every nonnegative index.

## Prior work and verification

Tani Akinari recorded the equivalent formula $\lfloor(2n+5)/5\rfloor-\lfloor(n+2)/3\rfloor$ in the same OEIS entry on 7 August 2013. To see the equivalence, write $m=n+3$. Layman’s difference is $\lceil 2m/5\rceil-\lceil m/3\rceil$. Replacing each ceiling by an integer floor gives $\lfloor(2n+10)/5\rfloor-\lfloor(n+5)/3\rfloor$, and removing one from both floors gives Akinari’s expression. The proof here independently verifies the identity by counting solutions. [OEIS formula section](https://oeis.org/A008676/internal)

- [Lean proof](../../OpenMath/A008676.lean) counts the actual finite set of solution pairs. It proves the set decomposition, the period step, and all initial cases. Integer division in the theorem expresses the two floors.
- [Exact arithmetic checker](check.py) enumerates all pairs with $3x+5y\le 5000$ and compares their counts with both formulas.
