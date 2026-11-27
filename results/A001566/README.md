# Counterexamples to McGarvey’s squarefreeness conjecture

Let $x_0=3$ and $x_{n+1}=x_n^2-2$. In a 2004 comment, Gerald McGarvey conjectured squarefreeness for the numbers obtained by writing the sequence terms as $8a+7$. The listed quotients begin $0,1,55,121771$, which are obtained by dividing $x_n-7$ by $40$ for $n=1,2,3,4$. We give positive counterexamples for both denominators. [Original sequence and conjecture](https://oeis.org/A001566/internal)

Both quotients are integers for every $n\ge1$, since $x_1=7$ and $7^2-2\equiv7\pmod{40}$.

## Printed denominator of eight

The recurrence gives $x_1=7$, $x_2=47$, and $x_3=2207$. Thus

```math
\frac{x_3-7}{8}=275=5^2\cdot 11.
```

## Denominator of forty from the listed examples

Reduce the recurrence modulo $40\cdot19^2=14440$. Each residue determines the next by squaring and subtracting two. Starting at index zero gives

```text
3, 7, 47, 2207, 4567, 6127, 10567, 11407, 807, 1447, 7.
```

In particular $x_{10}\equiv7\pmod{14440}$. Since $x_{10}>7$, the positive integer $(x_{10}-7)/40$ is divisible by $19^2$. The return to residue seven from index $1$ to index $10$ repeats every nine steps, so the same square divides the positive quotient at every index $10,19,28,\ldots$.

## Verification and scope

- [Lean proof](../../OpenMath/A001566.lean) checks both positive witnesses and the repeating family. Each witness proves exact divisibility by the corresponding denominator and the presence of a square divisor greater than one.
- [Arithmetic verification](check.py) reproduces the witnesses using exact Lucas numbers and independently checks the modular orbit. The source gives $x_n=L_{2^{n+1}}$; this also follows from $L_2=3$ and $L_{2k}=L_k^2-2(-1)^k$.
- The scope is the squarefreeness clause. Searches of the OEIS entry, mathematical literature by sequence ID, and TrureTuring did not locate an earlier account of either positive counterexample. [Source history](https://oeis.org/A001566/internal)
