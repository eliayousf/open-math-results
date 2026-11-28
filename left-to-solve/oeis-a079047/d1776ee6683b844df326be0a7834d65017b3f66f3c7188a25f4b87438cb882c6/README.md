# oeis-a079047

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a079047) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/2753cefb1be3fab7e42aac667fcb564b84ca938d)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a079047.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

[OEIS A079047](https://oeis.org/A079047) records a first term of 1. The merged Lean statement by @matchalabubu15 highlights that this first term is already a square and records T. D. Noe's two later counterexamples. The Lean disproof checks the first term directly.
