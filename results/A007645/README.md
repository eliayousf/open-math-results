# Tisdale’s union identity for generalized cuban primes

This is a Lean formalization of a known finite-field characterization. Daniel Tisdale recorded the sequence identity in July 2009. The equivalent root criterion for $p\ne3$, with the order argument below, appears in Michigan State’s Spring 2016 algebra solutions, exercise 12.5.9(a). [OEIS conjecture](https://oeis.org/A007645/internal) · [Prior exposition](https://users.math.msu.edu/users/bellro/mth419Hss16/mth419Hss16_homework.pdf#page=41)

## Statement

The primes in A007645 are exactly the union of A002383 and A162471. A007645 permits the characterization $p\bmod3\in\{0,1\}$ for primes $p$. A002383 lists prime values of $k^2+k+1$, and A162471 lists prime divisors of those quadratic values that are absent from A002383. Their union thus consists of the primes $p$ dividing $k^2+k+1$ for at least one natural number $k$. [A007645](https://oeis.org/A007645/internal) · [A002383](https://oeis.org/A002383) · [A162471](https://oeis.org/A162471)

## Proof

The prime $3$ divides $1^2+1+1$. For any other prime $p$, a root $z$ of $X^2+X+1$ in $\mathbb{F}_p$ is nonzero because the constant term is $1$. It differs from $1$ because the polynomial takes the value $3$ there. The identity $(X-1)(X^2+X+1)=X^3-1$ then gives $z^3=1$. Thus $z$ has order $3$ in the multiplicative group, so $3$ divides $p-1$.

Conversely, if $3$ divides $p-1$, Cauchy’s theorem gives a unit of order $3$ in $\mathbb{F}_p$. The same factorization gives $z^2+z+1=0$ because $z-1$ is nonzero. A natural representative of $z$ gives the required integer $k$.

## Verification

- [`OpenMath.A007645.main`](../../OpenMath/A007645.lean) proves the set equivalence for every natural number $p$. It checks both directions of the root criterion and the translation between the sequences and divisibility.
- [The exact arithmetic verifier](check.py) evaluates the quadratic across residue classes for every prime through $3000$ and checks sample initial terms of all three OEIS sequences.
