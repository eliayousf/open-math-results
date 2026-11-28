# oeis-a055938

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a055938) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/a6f44d11ab4ebdb85b257ae9a2b37add1d78139e)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a055938.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

This formalizes the complement recurrence attributed to Ralf Stephan in the [OEIS A055938 entry](https://oeis.org/A055938). The proof groups the missing integers into the gaps between successive even-indexed blocks of [A005187](https://oeis.org/A005187).
