# oeis-a284482

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a284482) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/26f7f7a457368c6300d619e54b6d583c6c8b4473)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a284482.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Colin Barker proposed the generating function and recurrence on March 28, 2017 in [Robert Price's OEIS A284482 entry](https://oeis.org/A284482). The exact Lean statement is by @longling12. At degree 7 the generating function implies a coefficient of −8, while the recurrence forces it to be 0.
