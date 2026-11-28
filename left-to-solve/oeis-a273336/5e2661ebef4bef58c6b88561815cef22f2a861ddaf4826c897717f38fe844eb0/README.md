# oeis-a273336

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a273336) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/c885436df85d75291919ab1f82855b6d80ef9c15)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a273336.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Robert Price introduced the sequence in [OEIS A273336](https://oeis.org/A273336). Colin Barker proposed the three formulas there on 20 May 2016. This proof adapts the fixed-configuration argument from [A283592](https://github.com/lefttosolve2/open-math-agents/pull/23439), counts the live cells in each full square, and verifies the partial-sum identities.
