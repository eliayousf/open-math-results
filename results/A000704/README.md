# Mathar’s recurrence for even involutions

Let $a(n)$ count the even permutations of $n$ labels whose square is the identity. For every $n\ge 5$, we prove

```math
a(n)-3a(n-1)+3a(n-2)-a(n-3)
 -(n-1)(n-3)a(n-4)+(n-3)(n-4)a(n-5)=0.
```

R. J. Mathar recorded this recurrence as a conjecture on 3 June 2014. The lower bound on $n$ makes all six indices nonnegative, in keeping with the entry’s offset of zero. [OEIS A000704](https://oeis.org/A000704/internal)

## Proof

Write $b(n)$ for the number of odd involutions on $n$ labels. An involution fixes the last label or pairs it with one of the remaining labels. In the second case, the transposition reverses the parity of the involution on the other labels. For $m\ge2$, this gives

```math
a(m)-a(m-1)=(m-1)b(m-2),\qquad
b(m)-b(m-1)=(m-1)a(m-2).
```

The third backward difference of $a(n)$ is therefore

```math
\begin{aligned}
a(n)-3a(n-1)+3a(n-2)-a(n-3)
 &= (n-1)b(n-2)-2(n-2)b(n-3)+(n-3)b(n-4)\\
 &= (n-1)\bigl(b(n-2)-b(n-3)\bigr)
   -(n-3)\bigl(b(n-3)-b(n-4)\bigr)\\
 &= (n-1)(n-3)a(n-4)-(n-3)(n-4)a(n-5).
\end{aligned}
```

This is the claimed recurrence.

## Scope of verification and prior work

- The [Lean proof](../../OpenMath/A000704.lean) uses the published formula $a(n)=\sum_{j=0}^{\lfloor n/4\rfloor}\binom{n}{4j}(4j-1)!!$, with the $j=0$ summand equal to one. Pascal’s identity and the double-factorial recurrence give the two parity recurrences in Lean, then integer algebra gives the identity for every $n\ge5$. Choosing the moved labels and pairing them explains the counting formula. [OEIS definition and formula](https://oeis.org/A000704/internal)
- The [exact arithmetic verifier](check.py) uses factorial quotients and exhaustive permutation enumeration through size eight. It checks the recorded initial terms and the recurrence through index 300.
- Mathar recorded the same recurrence for the **odd** involution sequence on 30 May 2014. Applied to the total number of involutions, the fixed-or-paired count in the proof gives the same recurrence. The earlier odd formula therefore also implies the even formula by subtraction. Glebsky, Licón, and Rivera give the broader even and odd generating functions. Proof priority for the even case remains unresolved. [OEIS A001465](https://oeis.org/A001465) · [On the number of even roots of permutations](https://arxiv.org/abs/1907.00548)
