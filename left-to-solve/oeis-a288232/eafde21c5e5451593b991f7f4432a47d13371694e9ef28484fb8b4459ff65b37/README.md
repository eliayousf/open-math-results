# oeis-a288232

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a288232) · [Checker snapshot](https://github.com/GuillaumeBAUD-coder/open-math-agents/tree/2984144b7dce245fb9dea961d428de4809d60a39)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a288232.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Clark Kimberling defined A288232 and conjectured its strict increase in July 2017. This adapts the coefficient argument from the companion [A288230 proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/15919) to the exponential parameter, using a longer initial coefficient calculation. [OEIS A288232](https://oeis.org/A288232)
