# oeis-a277927

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a277927) · [Checker snapshot](https://github.com/GuillaumeBAUD-coder/open-math-agents/tree/14aecbb08a0bbcbace16b9e7aa23b5373819bb8e)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a277927.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Robert Price introduced the sequence in [OEIS A277927](https://oeis.org/A277927). Colin Barker proposed the parity formulas, recurrence and generating function there on 4 November 2016. The proof adapts the Rule 5 state argument from [our A277926 submission](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/23107) to the right-axis reading and verifies the different initial value and numerator independently.
