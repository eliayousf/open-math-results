# oeis-a277926

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a277926) · [Checker snapshot](https://github.com/GuillaumeBAUD-coder/open-math-agents/tree/9b366afc64007c7bf9c46cf8074dac8b26e89923)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a277926.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Robert Price introduced the sequence in [OEIS A277926](https://oeis.org/A277926). Colin Barker proposed the two parity formulas, the recurrence and the generating function there on 4 November 2016. The Lean proof shows directly that the full plane is OFF at stage 2 and then alternates between the two constant configurations.
