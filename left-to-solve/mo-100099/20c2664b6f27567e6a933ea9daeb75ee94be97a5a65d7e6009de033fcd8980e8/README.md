# mo-100099

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/mo-100099) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/270afd7500d012f56ed9724841a37b7a4c82835f)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_mo_100099.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

This formalizes the stabilization assertion in [Hao Chen’s MathOverflow question](https://mathoverflow.net/questions/100099/how-does-the-distribution-of-erd%C5%91s-number-evolve-over-time-how-to-build-a-mode), as stated by @chris01-dev. The proof bounds the publication years along a walk by its length times the common career length, plus the starting year.
