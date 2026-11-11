We present a formalization, in the Lean~4 proof assistant with the Mathlib library, of the
partition function $p(n)$ and of four classical theorems about it: Euler's generating function,
Ramanujan's congruence $p(5n+4)\equiv 0 \pmod 5$, the Hardy--Ramanujan asymptotic formula and
Rademacher's exact series. Euler's identity $\sum_{n\ge 0}p(n)X^n=1/(X;X)_\infty$ is proved
completely, over an arbitrary field. Ramanujan's congruence is proved by his elementary argument
relative to one classical statement that is formalized but not yet proved, namely Jacobi's
identity for $(X;X)_\infty^3$. The two analytic theorems are stated formally, with Dedekind sums,
the sums $A_k(n)$ and Rademacher's kernel defined in full; we prove the parts of their proofs
that do not need the circle method (reality and the trivial bound of $A_k(n)$, the Bessel form of
the terms, the saddle-point computation) and reduce Rademacher's theorem to two analytic
statements. The development comprises about 950 lines and compiles against current Mathlib.
Exactly ten statements remain unproved; we list them, together with numerical evidence for their
correctness.
