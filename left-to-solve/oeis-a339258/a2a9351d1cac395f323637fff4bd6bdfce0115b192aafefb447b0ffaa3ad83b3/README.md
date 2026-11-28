# oeis-a339258

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a339258) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/69048dba62cf5cee76f2fa030e05f3e59290a707)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a339258.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Omar E. Pol’s row-sum conjecture appears in [OEIS A339258](https://oeis.org/A339258). The equivalent divisor-count convolution is recorded in [OEIS A006128](https://oeis.org/A006128). This Lean proof formalizes the correspondence obtained by deleting a specified positive number of equal parts.
