# Open Math Results

## A000033 · Van Hoeij’s congruence

For every positive integer $n$ and every prime $p$, the terms of OEIS A000033 satisfy

```math
a(n)+2a(n+p)+a(n+2p)\equiv 0\pmod p.
```

Published by Elia Yousf. Codex found the proof and wrote the Lean formalization. The result page gives the argument, its relation to van Hoeij’s 2019 note, and the scope of the checks. [Written proof and sources](results/A000033/README.md) · [Lean proof](OpenMath/A000033.lean)


## Ten OEIS conjectures

Lean proofs or counterexamples and reproducible exact arithmetic checks. Each write-up records prior work and the scope of the result. Elia Yousf coordinated the work with Codex, which developed the proofs, formalizations, and checks.

- [A000704](results/A000704/README.md). Proved Mathar’s recurrence for even involutions. The write-up credits the earlier related odd-involution formula.
- [A001481](results/A001481/README.md). Verified the classical zero-or-equal classification for two sums of squares adding to a power of two.
- [A001566](results/A001566/README.md). Disproved squarefreeness under both the printed and example-implied normalizations.
- [A003477](results/A003477/README.md). Disproved the printed identity at n = 4 and proved the correction including the constant term.
- [A005994](results/A005994/README.md). Proved Mathar’s adjacent-sum identity by a multiplicity bijection and a binomial telescope.
- [A006364](results/A006364/README.md). Proved Yanev’s binary-count formula and credited Stephan’s earlier identities that imply it.
- [A007645](results/A007645/README.md). Formalized the set-union identity using the previously documented finite-field characterization.
- [A008676](results/A008676/README.md). Proved Layman’s floor formula by counting partitions into 3s and 5s. Akinari gave an equivalent formula in 2013.
- [A020964](results/A020964/README.md). Proved Wu’s recurrence and generating function for the original silver-ratio floor sum.
- [A026796](results/A026796/README.md). Disproved the printed shift by four at n = 2 and proved the corrected shift by three.

## Run the checks

```sh
nix develop -c python3 scripts/check.py --fetch-cache
```

This builds the proof with pinned Lean and Mathlib versions, replays it in the Lean kernel, audits its axioms, and runs the exact Python arithmetic checks.
