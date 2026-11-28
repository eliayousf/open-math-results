# oeis-a284481

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a284481) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/1dbf21de2853ea53a3e51e133ee09945c8cb0385)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a284481.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Colin Barker proposed the generating function and recurrence on March 28, 2017 in [Robert Price's OEIS A284481 entry](https://oeis.org/A284481). The exact Lean statement is by @longling12. At degree 7 the generating function implies a coefficient of −16, while the recurrence forces it to be 0.
