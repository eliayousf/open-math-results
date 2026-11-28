# oeis-a048868

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a048868) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/370d2e58e839fe797f5075573bc99129548a6e77)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a048868.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Labos Elemer introduced the sequence in [OEIS A048868](https://oeis.org/A048868). Michael De Vlieger proposed the parity conjecture there on 21 May 2017. The proof injects the prime reduced residues into the nonprime residues for odd moduli using additive inverses and a separate treatment of the pair containing 2.
