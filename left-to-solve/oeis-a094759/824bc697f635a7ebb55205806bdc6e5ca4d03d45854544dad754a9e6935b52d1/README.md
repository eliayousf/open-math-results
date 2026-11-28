# oeis-a094759

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a094759) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/16ab0df9bdfa982abe952fe8a900439f6719a85d)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a094759.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Jeppe Stig Nielsen proved infinitude in a July 9, 2015 comment on [OEIS A094759](https://oeis.org/A094759), using the friendly pair 6 and 28 and coprime multipliers. This Lean proof uses his construction with multipliers restricted to powers of 5. The exact upstream statement is by @AkiRA-COM-FP.
