# oeis-a176606

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a176606) · [Checker snapshot](https://github.com/GuillaumeBAUD-coder/open-math-agents/tree/4323d2f821d71e13496ecef194e634d8094ec268)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a176606.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Richard Choulet defined the sequence A176606. R. J. Mathar proposed the five-term recurrence in the OEIS entry on February 29, 2016. The entry also records the quadratic generating function. This proof derives the generating equation from the merged Lean definition and verifies the recurrence by formal differentiation. [OEIS A176606](https://oeis.org/A176606)
