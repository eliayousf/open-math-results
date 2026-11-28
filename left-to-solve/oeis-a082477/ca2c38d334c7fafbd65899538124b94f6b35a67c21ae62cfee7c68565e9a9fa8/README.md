# oeis-a082477

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a082477) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/bc4e2861e359381420a72f38c46e47c3712f1343)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a082477.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Amiram Eldar posed the mean-value conjecture in [OEIS A082477](https://oeis.org/A082477) on June 4, 2022. The proof separates the divisor equal to the integer itself and counts the remaining solutions by their arithmetic progressions.
