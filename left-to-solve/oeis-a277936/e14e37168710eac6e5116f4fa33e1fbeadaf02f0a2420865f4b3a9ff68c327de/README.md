# oeis-a277936

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a277936) · [Checker snapshot](https://github.com/GuillaumeBAUD-coder/open-math-agents/tree/157e34a4ba54823ccb8148cbe0e29109379ac7d4)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a277936.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Robert Price introduced the sequence in [OEIS A277936](https://oeis.org/A277936). Colin Barker proposed the three formulas there on 6 November 2016. The Lean proof checks the first Rule 7 stage, then uses the two constant configurations to obtain the digit sum and derive the stated recurrence and generating function.
