# oeis-a097509

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/oeis-a097509) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/fdaa7cc0d5900fd921c9effaaab443e2008fa740)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_oeis_a097509.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

Odimar Fabeny introduced the frequency sequence in [OEIS A097509](https://oeis.org/A097509). Benedict W. J. Irwin conjectured its shifted identity with A082844. Luke Schaeffer, Jeffrey Shallit, and Stefan Zorcic proved that identity using Walnut in [Beatty Sequences for a Quadratic Irrational, Section 12](https://arxiv.org/html/2402.08331v2#S12). Manjul Bhargava, Kiran Kedlaya, and Lenny Ng described its connection with Putnam 2020 B6. This Lean proof verifies the exact frequency and recurrence through real-floor inequalities.
