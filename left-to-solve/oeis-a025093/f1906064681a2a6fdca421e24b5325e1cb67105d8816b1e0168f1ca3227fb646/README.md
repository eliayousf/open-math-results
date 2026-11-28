# oeis-a025093

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a025093) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/b49b1c19491d53457f46d7f4303835c1ff3f9788)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a025093.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Colin Barker conjectured the recurrence and generating function in [OEIS A025093](https://oeis.org/A025093) on 7 August 2019. The Lean proof takes two finite differences of the exact merged Lucas sum and derives both identities from the resulting weighted Lucas terms.
