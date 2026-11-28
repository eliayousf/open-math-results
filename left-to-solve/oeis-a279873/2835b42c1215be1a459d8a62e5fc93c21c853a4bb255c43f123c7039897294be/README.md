# oeis-a279873

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a279873) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/ab10421c61789033ff22b34991f9eb2f9391671d)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a279873.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Colin Barker proposed the recurrence and generating function in [OEIS A279873](https://oeis.org/A279873) on 22 December 2016. The Lean disproof compares their consequences at index 12. The recurrence forces the coefficient after multiplying by the denominator to be zero, while the generating function gives −10000.
