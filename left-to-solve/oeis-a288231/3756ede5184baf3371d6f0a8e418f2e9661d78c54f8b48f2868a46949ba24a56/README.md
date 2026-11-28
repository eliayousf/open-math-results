# oeis-a288231

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a288231) · [Checker snapshot](https://github.com/GuillaumeBAUD-coder/open-math-agents/tree/927945d4b47162a83a0bfac1cbc4e43e1d7600ba)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a288231.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Clark Kimberling defined A288231 and conjectured its strict increase in July 2017. This adapts the coefficient argument from the companion [A288230 proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/15919) to the cube-root parameter of the exact A288231 statement. [OEIS A288231](https://oeis.org/A288231)
