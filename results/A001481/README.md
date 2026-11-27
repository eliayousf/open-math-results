# Powers of two and sums of two squares

J. Lowell’s 14 January 2022 comment on OEIS A001481 asks whether two distinct terms can add to a power of two, apart from sums with zero. The entry allows zero as a square and omits $0+1=2^0$ from its explicit list of exceptions. [Original OEIS comment](https://oeis.org/A001481/internal)

For all $k\ge 0$, if $a,b$ are sums of two nonnegative integer squares and $a+b=2^k$, then $a=0$, $b=0$, or $a=b$. In particular, two distinct positive terms never add to a power of two. With a zero summand, the possible unordered pair is $\{0,2^k\}$, including $\{0,1\}$ at $k=0$. With equal positive summands, each is $2^{k-1}$ and $k\ge1$. Each power of two is a sum of two squares, by using $2^{2m}=(2^m)^2+0^2$ or $2^{2m+1}=(2^m)^2+(2^m)^2$.

## Proof

Write $a=x^2+y^2$ and $b=z^2+w^2$. For $k\ge 3$, the sum of the four squares is divisible by eight. A square is $0$, $1$, or $4$ modulo eight, and an odd integer has square congruent to $1$. Modulo four, the number of odd coordinates must therefore be zero or four. Four odd coordinates would give a sum congruent to $4$ modulo eight. Thus all four coordinates are even.

Halve the four coordinates. The new sum of four squares is $2^{k-2}$ and the two pair sums are $a/4$ and $b/4$. Repeat until the total is $1$, $2$, or $4$.

- For total $1$, the four squares are one $1$ and three zeros. One pair is zero.
- For total $2$, there are two $1$s and two zeros. The pair sums are $0$ and $2$, or $1$ and $1$.
- For total $4$, there is one $4$ and three zeros, or four $1$s. The pair sums are $0$ and $4$, or $2$ and $2$.

Multiplying the pair sums back by four at each step preserves equality and zero. This proves the classification.

## Prior work and verification

This is a classical corollary of Jacobi’s four-square theorem. For $k\ge1$, the theorem counts exactly 24 ordered, signed representations of $2^k$. For $k=2m+1$, the permutations and signs of $(2^m,2^m,0,0)$ already give 24 representations. For $k=2m\ge 2$, the permutations and signs of $(2^m,0,0,0)$ and $(2^{m-1},2^{m-1},2^{m-1},2^{m-1})$ account for the same total. Each list gives the same partition into pair sums. The elementary proof above uses modular arithmetic. Priority for Lowell’s exact formulation is unestablished. [Jacobi’s formula, NIST DLMF §27.13](https://dlmf.nist.gov/27.13)

- [Lean proof](../../OpenMath/A001481.lean) proves the classification over every natural exponent and all nonnegative summands.
- [Exact arithmetic check](check.py) enumerates all sums of two nonnegative squares up to $2^{20}$ and checks every unordered pair adding to $2^k$ for $0\le k\le 20$.
- The formalization and check were developed with Codex.
