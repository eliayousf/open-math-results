# oeis-a174808

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a174808) · [Checker snapshot](https://github.com/GuillaumeBAUD-coder/open-math-agents/tree/7487161da835495ef63cc05f1e64276d6b67d93a)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a174808.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Paul Barry introduced the binomial transform and its generating function in [OEIS A174808](https://oeis.org/A174808). R. J. Mathar stated the recurrence there on 10 February 2015. The formal proof uses Mathlib's quadratic identity for the large Schröder generating series, proves that substitution by (X+X^2) gives the statement's exact sum, and derives the recurrence by formal differentiation.
