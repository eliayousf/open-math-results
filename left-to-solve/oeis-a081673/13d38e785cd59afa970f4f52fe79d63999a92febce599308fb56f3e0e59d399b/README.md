# oeis-a081673

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a081673) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/88316af71fb1246c4a60a7f7658b2bc3ab0f1059)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a081673.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

R. J. Mathar proposed this recurrence in [OEIS A081673](https://oeis.org/A081673). Robert Israel confirmed it there by a differential equation in 2016. This Lean formalization instead uses a telescoping certificate for the two-binomial expression for the [central trinomial coefficients](https://oeis.org/A002426) and combines three shifts of their recurrence.
