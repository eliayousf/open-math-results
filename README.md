# Open Math Results

## A000033 · Van Hoeij’s congruence

For every positive integer $n$ and every prime $p$, the terms of OEIS A000033 satisfy

```math
a(n)+2a(n+p)+a(n+2p)\equiv 0\pmod p.
```

Published by Elia Yousf. Codex found the proof and wrote the Lean formalization. The result page gives the argument, its relation to van Hoeij’s 2019 note, and the scope of the checks. [Written proof and sources](results/A000033/README.md) · [Lean proof](OpenMath/A000033.lean)

## A002457 · Shunia’s square-root formula

For every positive integer $n$, the units digit in base $16^n$ of the integer square root of $(16^n+1)^{2n+1}$ is $(2n+1)\binom{2n}{n}$. [Written proof and sources](results/A002457/README.md) · [Lean proof](OpenMath/A002457.lean)

## Run the checks

```sh
nix develop -c python3 scripts/check.py --fetch-cache
```

This builds the proof with pinned Lean and Mathlib versions, replays it in the Lean kernel, audits its axioms, and runs the exact Python arithmetic checks.
