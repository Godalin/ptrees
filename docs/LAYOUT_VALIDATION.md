# Local validation

## Layout snapshot

The structural cleanup at `6194bdf` preserved the theory baseline
`92e0841` modulo import paths: 190 Coq modules, 65 moves, no proof changes.
Its clean full build and 74 independent kernel checks passed. The initial
single-process aggregate check failed with a universe inconsistency; it was
not counted as passing.

The historical source-invariance check remains pinned to those two revisions.
`python3 tools/audit_layout.py` also reports the **current** dependency graph,
excluding the import-only harness from substantive client counts. The stored
report reproduces exactly.

## Universe repair

The [root-cause report](UNIVERSE_CONSISTENCY.md) identifies the two incompatible
legacy Enum/Enum regressions and their migration to Enum/FreeOmega Enum.
It also records the preserved regression properties and the inherited
logical dependencies of the revised quotient-mass separation proof.

Current checks:

- Full `opam exec -- dune build` passes, including `AllImports.v`.
- All 190 pre-existing modules load together in ordinary Coq, in both
  forward and reverse order.
- `python3 tools/check_aggregate.py` verifies complete aggregate-import
  coverage; CI runs this guard before building.
- A single `coqchk` process loads `AllImports` (hence all 190 other modules)
  and rechecks both repaired regressions plus the original failing
  `PEuttAlgebra` module: **PASS**. All universe constraints coexist during
  those proof checks; this is not a set of isolated module checks.
  CI now runs this same command after building.
- The expanded audit rechecking **every proof** in all 191 modules was
  manually interrupted after roughly 40 minutes without a final result.
  A repeat of the original 74-module audit was also interrupted while still
  computing. Neither is counted as passing. An optional VM-enabled run hit
  a Coq checker assertion, documented in the root-cause report.
- `git diff --check` passes; no new axiom or unfinished proof is added.
  Core/Prob/Eq/Semantics implementations are unchanged.

Reproduce the build and the **passed single-process regression check** with:

```sh
python3 tools/check_aggregate.py
opam exec -- dune build
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Regression.Infrastructure.AllImports \
  -norec PTree.Regression.Backend.UnifiedFrontierEnum \
  -norec PTree.Regression.Semantics.CanonicalPartialDivergence \
  -norec PTree.Regression.Semantics.PEuttAlgebra
```

The command loads every project module, checks the four listed modules, and
trusts the compiled proofs of the other modules. To additionally recheck
every project's proof in that shared context, run
`python3 tools/check_aggregate.py --kernel`; this broader audit is available
but has **not** completed in this repair. Native-computation tests may emit
the standard VM fallback warning when native compilation is disabled.

These are local results. No remote CI success is asserted here.
