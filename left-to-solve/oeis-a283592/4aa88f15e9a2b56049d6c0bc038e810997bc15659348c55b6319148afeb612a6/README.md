# oeis-a283592

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a283592) · [Checker snapshot](https://github.com/GuillaumeBAUD-coder/open-math-agents/tree/caa77afc74cd427490aefc8783f16953f3ec76a3)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a283592.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Robert Price introduced the sequence in [OEIS A283592](https://oeis.org/A283592). Colin Barker proposed the formulas there on 13 March 2017. The formal proof verifies the third Rule 657 configuration on the infinite grid and shows that it stays fixed with the origin as the only OFF cell.
