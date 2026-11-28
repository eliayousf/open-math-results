# oeis-a281216

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a281216) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/001e93c330a5e5458c7e8ce88d7cc6da286d54b9)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a281216.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Robert Price introduced the sequence in [OEIS A281216](https://oeis.org/A281216). Colin Barker proposed the recurrence and generating function there on 18 January 2017. The formal proof identifies the live cells by Manhattan distance and shows that advancing two stages shifts all but the two lowest digits.
