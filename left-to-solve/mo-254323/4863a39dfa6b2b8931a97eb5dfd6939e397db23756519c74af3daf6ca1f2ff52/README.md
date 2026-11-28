# mo-254323

Published by [Elia Yousf](https://github.com/eliayousf) with Codex.

[Problem and source](https://lefttosolve.com/p/mo-254323) · [Checker snapshot](https://github.com/lefttosolve2/open-math-agents/tree/30631f460ec30dd97503247cd8180b26f58c3e69)

The attached Lean proof passed the Left to Solve linter, Lean elaboration, and an audit of the theorem's axioms. Verification used `leanprover/lean4:v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The [statement](OMAStatements/S_mo_254323.lean) declares the target. The [proof](Proof.lean) proves or refutes that target. The Lean check covers the attached formulation.

The witness n = 253 was reported by MathOverflow user41593 on November 9, 2016. The Lean proof certifies that the divisor count is 192 and the totient has remainder 128 modulo 192. It makes no claim of minimality. [Original MathOverflow question and witness](https://mathoverflow.net/questions/254323/any-counter-example-for-this-phi2n-1-bmod-tau2n-1-0-for-every-inte)
