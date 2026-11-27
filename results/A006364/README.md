# Yanev’s signed formula for OEIS A006364

Let $s(k)$ be the number of ones in the binary expansion of $k$. In increasing order, with the first index equal to one, let $a(n)$ list the integers $m\ge 0$ for which $s(\lfloor m/2\rfloor)$ is even. Velin Yanev conjectured the following formula on 21 December 2016. [OEIS A006364](https://oeis.org/A006364/internal) · [OEIS A000120](https://oeis.org/A000120)

```math
a(n)=2n+(-1)^{n-s(n-1)}-\frac{3+(-1)^n}{2}qquad(n\ge 1).
```

## Proof

Write $p(k)=s(k)\bmod 2$. In the block $4k,4k+1,4k+2,4k+3$, removing the final binary bit gives $2k$ for the first pair and $2k+1$ for the second. Their binary weights are $s(k)$ and $s(k)+1$. Exactly the pair

```math
4k+2p(k),\qquad 4k+2p(k)+1
```

belongs to the sequence. Since the blocks appear in increasing order, this pair occupies the one-based positions $2k+1$ and $2k+2$.

Now write $n-1=2k+e$, with $e\in\{0,1\}$. The block count gives $a(n)=4k+2p(k)+e$. Also $s(n-1)=s(k)+e$, so $n-s(n-1)=2k+1-s(k)$. Its sign is $2p(k)-1$, and $(-1)^n=2e-1$. Substituting these signs into the claimed formula gives $4k+2p(k)+e$.

## Verification and prior work

- The [Lean proof](../../OpenMath/A006364.lean) starts from the binary digit-sum predicate and proves that the block formula gives its unique increasing enumeration. It proves the signed identity over the integers for every positive index.
- The [Python check](check.py) directly enumerates qualifying integers and compares the conjectured formula through the first 100,000 terms. A separate exact comparison matched all 10,000 entries in the [official table](https://oeis.org/A006364/b006364.txt).
- Ralf Stephan recorded the relation to the even-weight sequence A001969 in October 2003 and an explicit formula for A001969 in September 2003. Combining those earlier identities also yields Yanev’s formula. [OEIS A006364](https://oeis.org/A006364/internal) · [OEIS A001969](https://oeis.org/A001969/internal)
