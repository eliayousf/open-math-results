# oeis-a281214

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a281214) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/65cd9f113ee48007468bcb4ff7f009b30ec7e1d4)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a281214.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Robert Price introduced the sequence in [OEIS A281214](https://oeis.org/A281214). Colin Barker proposed the recurrence and generating function there on 18 January 2017. This proof adapts the Manhattan-distance argument from [the A281216 proof](https://github.com/lefttosolve2/open-math-agents/pull/23658) and checks the separate base-10 recurrence and generating-function numerator.
