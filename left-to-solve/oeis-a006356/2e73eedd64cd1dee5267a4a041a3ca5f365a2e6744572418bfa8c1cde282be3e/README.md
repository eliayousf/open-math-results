# oeis-a006356

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a006356) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/03c5b3d61238c35edb5c8735c5cfb01d971f056d)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a006356.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

The merged statement credits Benoît Cloitre's asymptotic conjecture and Paul D. Hanna's generating function, both on [OEIS A006356](https://oeis.org/A006356), and @Assassino9931 for the Lean statement. Its own introduction records the one-plate generating function. The disproof formalizes that boundary case. Every sequence term and the proposed growth rate equal 1, so the asymptotic forces the leading coefficient to equal 1.
