# oeis-a285777

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a285777) · [Checker snapshot](https://github.com/GuillaumeBAUD-coder/open-math-agents/tree/e5874e880ebc0e6d80ae253de3ffca71064c9bc2)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a285777.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Robert Price introduced the sequence in [OEIS A285777](https://oeis.org/A285777). Colin Barker proposed the parity formulas, recurrence and generating function there on 26 April 2017. The formal proof checks the fourth Rule 89 stage on the infinite grid and proves that the plane then alternates between the two constant configurations.
