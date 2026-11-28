# oeis-a068912

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a068912) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/9048878df6434472af65c23f749349f2bd4ee949)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a068912.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Henry Bottomley introduced the sequence in [OEIS A068912](https://oeis.org/A068912). Peter Luschny proposed the floor formula on 20 September 2020, and Herbert Kociemba proved it in the entry by bounding the smaller-root term. The Lean formalization derives the exact walk counts by splitting on the first step and formalizes Kociemba's floor estimate.
