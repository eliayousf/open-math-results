# oeis-a283646

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a283646) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/01f6e9ce6566ff4499bcd52e5dbf3f1638d02b81)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a283646.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Colin Barker proposed the generating function and recurrence on March 14, 2017 in [Robert Price's OEIS A283646 entry](https://oeis.org/A283646). The exact Lean statement is by @longling12. At degree 15 the generating function gives coefficient 256, whereas the stated recurrence makes it 0.
