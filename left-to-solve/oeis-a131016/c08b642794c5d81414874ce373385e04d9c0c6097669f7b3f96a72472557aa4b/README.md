# oeis-a131016

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a131016) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/eebcdee75a7a762f1cd113f07fff6f8b1bf8f4a5)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a131016.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

T. D. Noe observed in a September 26, 2007 comment on [OEIS A131016](https://oeis.org/A131016) that a semiprime s is attained at the index s − 1. The formalization checks minimality directly: every smaller residue representative equal to 1 modulo s − 1 is 1, which is excluded by the semiprime condition. The exact Lean statement is by @AkiRA-COM-FP.
