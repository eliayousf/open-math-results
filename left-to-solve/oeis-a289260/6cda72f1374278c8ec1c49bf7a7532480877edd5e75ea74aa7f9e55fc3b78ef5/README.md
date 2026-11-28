# oeis-a289260

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a289260) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/deadee208fccc0051931aef6f3cd9ddaa4152980)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a289260.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Clark Kimberling posed strict increase in [OEIS A289260](https://oeis.org/A289260). Colin Barker supplied the rational generating function there on July 14, 2017. The Lean proof derives Barker’s identity from the signed floor coefficients and uses it to show that every successive difference is positive.
