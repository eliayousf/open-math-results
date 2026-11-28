# oeis-a288230

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a288230) · [Checker snapshot](https://github.com/GuillaumeBAUD-coder/open-math-agents/tree/19c303aa6f4dc57d3f4e927288b58ac6e3a82c28)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a288230.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Clark Kimberling defined A288230 and conjectured its strict increase in July 2017. The proof shows that every coefficient after the first is at least 3/2 times its predecessor. [OEIS A288230](https://oeis.org/A288230)
