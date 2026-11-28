# oeis-a281215

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a281215) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/18b4afac787c1678cb30f2eb0a6ed6c9d6bfa1a9)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a281215.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Robert Price introduced the sequence in [OEIS A281215](https://oeis.org/A281215). Colin Barker proposed the recurrence and generating function there on 18 January 2017. The proof adapts the Manhattan-distance argument from [A281216](https://github.com/lefttosolve2/open-math-agents/pull/23658) and checks the origin-first digit sum, its recurrence and the generating-function numerator.
