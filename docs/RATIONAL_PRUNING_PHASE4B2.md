# Phase 4b.2 — shared weighted-list pruning

Baseline: accepted `e8a7524` (Phase 4b.1). Phase 4 remains **OPEN**.

This increment extracts zero-entry pruning from the rational backend without
changing its carrier, equality, lifting, support or coupling definitions.
Production still uses `EnumQ A = list (nnQ * A)` and the existing bounded
`SubEnumQ` wrapper. There is no runtime representation conversion layer.

## Shared mathematics and production use

`Prob/Backend/Common/FinitePruning.v` defines `finite_prune discard` over
arbitrary coefficient types. It preserves the order and multiplicity of
retained entries; it neither aggregates atoms nor normalizes weights.
The predicate acts on weights, so no equality/inhabitation/countability
requirement is imposed on values (which may be continuations).

The raw API proves append and value-map compatibility, exact membership,
idempotence, and compatibility with a scalar map preserving the discard test.
For ordinary `numDomainType` scalars it additionally proves:

- nonnegativity is preserved;
- deleting arbitrary entries decreases nonnegative expectations;
- deleting exactly zero weights preserves **all** expectations, with no
  nonnegative or bounded-test restriction on the observable;
- checked `FiniteEnum` and `FiniteSubdist` pruning preserves their invariants.

Only `EnumQ/FrontierLift.v` changes among production clients. Its old recursive
`enumQ_prune` becomes the specialization of `finite_prune` at the `nnQ` zero
test. The old and new functions are definitionally equal, checked by
`native_prune_exact` against a regression-only copy of the frozen recursion.
Three old proof bodies now reuse shared append/map/membership results. Two
relational-bind proof bodies use explicit `change` to expose the original
goal instead of relying on broad `cbn` to preserve a wrapper name.

All theorem statements and instances retain their original signatures.
`enumQ_meas_eq`, `enumQ_ae`, indexed coupling and its relation are not moved
into Common or redefined. Zero pruning remains distinct from the position
operation introduced in Phase 4b.1, which deliberately retains zero slots.

## Regression and preservation gate

`Regression/Backend/RationalPruning.v` checks:

- old recursive operation and new delegation agree by reflexivity;
- the native equality still means indexed equality coupling of the same
  pruned lists;
- `Qval` commutes with zero pruning (no new scalar equality axiom);
- order, duplicates, all-zero and empty-carrier behavior;
- half mass stays half mass, without renormalization;
- arbitrary signed-observable preservation and exact nonzero membership;
- shared subdistribution mass and bound preservation;
- arbitrary discard really can lose mass;
- a large-universe carrier;
- importing Common does not import rational/semantic/FreeOmega infrastructure.

`tools/audit_rational_pruning.py` reconstructs the sole changed production
file from `e8a7524` by five explicit proof edits and one definition extraction.
All other old tracked files are byte-for-byte frozen except the two sorted
AllImports additions, regression registration, and generated architecture
report. Historical phase audits and compiled snapshots are not loosened.

The compiled gate independently replays the frozen `FrontierLift.v` in a
fresh namespace and compares all 31 declarations, **including instances**,
using `Check @` and `Print Assumptions`. Only that historical namespace and
printer whitespace are normalized. It also requires all 29 new common/test
constants to be closed under the global context. No new semantic capability,
logical axiom, checker bypass or proof irrelevance is introduced.

## Local validation

All of the following completed successfully locally:

```sh
opam exec -- dune build
python3 -m unittest discover -s tools -p 'test_*.py'
python3 tools/audit_architecture.py --check
opam exec -- python3 tools/audit_rational_pruning.py
opam exec -- python3 tools/audit_assumptions.py --check
opam exec -- python3 tools/audit_soundness.py --check
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Prob.Backend.Common.FinitePruning \
  -norec PTree.Prob.Backend.EnumQ.FrontierLift \
  -norec PTree.Prob.Backend.EnumQ.Measure \
  -norec PTree.Prob.Backend.EnumQ.FinitePresentation \
  -norec PTree.Prob.Backend.SubEnumQ.FreeOmega.JointSoundness \
  -norec PTree.Regression.Backend.RationalPruning \
  -norec PTree.Regression.Infrastructure.AllImports
```

Results:

- full build, including AllImports;
- 107 tool tests; architecture and generated report agree;
- exact source conservation and all 31 frozen client declarations replayed;
- all 29 new constants closed under the global context;
- all 505 existing exact compiled contracts and assumptions unchanged;
- soundness checks: 199 exact contracts, 36 generic quotient endpoints,
  18 finite-real joint endpoints, 80 native MathComp endpoints;
- seven-module joint `coqchk -norec`, started after the full build completed.

An early compiled-audit attempt, before the new regression had compiled,
correctly rejected its missing `.vo`; it was not counted as a pass. The full
audit was rerun successfully after the regression compiled.

The kernel check checks the named bodies while trusting their dependencies;
it is not a whole-library recursive kernel audit. The ordinary full build
includes the two unchanged Gate M modules and is therefore not claimed wholly
universe-checked. Neither Gate M module is in the targeted kernel-check set.
CI is intentionally ignored and no environment/checker settings were changed.

Counts: 283 -> 285 theory modules; 75 -> 76 Regression modules; 281 -> 283
Gate S modules; 2 -> 2 Gate M modules. The common module contributes 14
definitions/lemmas, and the regression contributes 15 definitions/examples.

## Remaining rational migration

This is a bounded preparation step, **not Phase 4 completion**. Production
scaling/bind, atom mass and finite presentation still require their ordinary
rational/shared-carrier migration. The accepted representation certificate
continues to be regression-only. Do not remove `nnQ` or introduce an old/new
conversion backend in order to bypass those clients.
