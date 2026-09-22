# Phase 4b.3 — shared finite positional presentation

Baseline: accepted `b49fcf3`. Phase 4 remains **OPEN**.

## Scope and mathematical boundary

`Prob/Backend/Common/FinitePresentation.v` extracts the representation of a
weighted list over its finite ordinal positions. For arbitrary coefficient
type `W` and value type `A`, it provides:

```text
mu : list (W * A)
position mu = ordinal (length mu)
entry / weight / value at each position
positions mu : list (W * position mu)
decode (positions mu) = mu
```

The last equality is exact list equality: order, repeated values and zero
weights survive. There is no support pruning, sorting, aggregation or
normalization. Values need neither equality nor an inhabitant; functions and
large-universe values are supported. The ordinal carrier remains finite even
when the value carrier is not.

This is distinct from `FinitePositions` (natural-number indexing with a
starting offset) and `FinitePruning` (entry removal). Neither of those modules
is changed. The new module owns only finite presentation and its invariants,
not equality/coupling/transport semantics.

For `numDomainType` coefficients the shared module proves nonnegativity,
exact arbitrary-observable expectation preservation, and mass preservation.
`finite_enum_positions` and `finite_subdist_positions` package those facts in
the existing shared records. Their decode laws compare raw lists rather than
proof-carrying record equality; no proof irrelevance is used.

## Production reuse

The only modified production module is `EnumQ/FinitePresentation.v`:

- five positional definitions delegate to the shared raw operations;
- `enumQ_positions_decode` uses the shared exact decode theorem.

The weight/value wrappers explicitly retain their original dependent index
type, `enumQ_position mu`. The elaborated signatures are checked independently.
The old definitions and new delegations agree definitionally, including the
actual finite weighted enumeration, not just its observations.

All remaining source in that module is unchanged. In particular the native
`sem_lift` decoding proof, the `SubEnumQ` bounded wrapper and lifting theorem,
weighted expectation formulas and finite atom-sum theorem remain backend-owned.
`FiniteTransport`, indexed coupling, pruning, scale/bind, atom-mass definitions,
FreeOmega, MathComp and Gate M are untouched.

`EnumQ` is still the old `list (nnQ * A)` carrier. `SubEnumQ` still wraps that
carrier. There is no production use of the Phase 4a conversion certificate.

## Regression and conservation gate

`RationalPresentation.v` checks the frozen ordinal/entry/enumeration definitions
against the production implementation by reflexivity, exact native and shared
decoding, the unchanged raw bounded presentation, and coefficient-mapped
decoding through `Qval`. The latter is a decoded-list compatibility check,
not a new generic scalar-transport theorem.

It also checks zero and duplicate slots, explicit positional indices,
empty and function carriers, signed observables, shared subdistribution mass
and bounds, and a large-universe carrier. Common-only negative import checks
ensure semantic interfaces, `nnQ` and FreeOmega are not loaded by Common.

`audit_rational_presentation.py` reconstructs the production client from
`b49fcf3`: only five exact definition replacements, their Common import and
one exact proof replacement are allowed. Every other old tracked file is
byte-for-byte frozen except the two sorted AllImports additions, regression
registration, and generated architecture report. Historical phase audits and
compiled snapshots are unchanged.

The compiled check independently elaborates the frozen source in a fresh
namespace and compares all 13 client declarations' types and assumptions.
Only the fresh historical namespace and printing whitespace are normalized.
All 39 new shared/test constants must be closed under the global context.

## Local verification

All of these commands completed successfully locally:

```sh
opam exec -- dune build
python3 -m unittest discover -s tools -p 'test_*.py'
python3 tools/audit_architecture.py --check
opam exec -- python3 tools/audit_rational_presentation.py
opam exec -- python3 tools/audit_assumptions.py --check
opam exec -- python3 tools/audit_soundness.py --check
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Prob.Backend.Common.FinitePresentation \
  -norec PTree.Prob.Backend.EnumQ.FinitePresentation \
  -norec PTree.Prob.Backend.EnumQ.FreeOmega.NativeTransport \
  -norec PTree.Prob.Backend.SubEnumQ.FreeOmega.NativeTransport \
  -norec PTree.Prob.Backend.SubEnumQ.FreeOmega.JointSoundness \
  -norec PTree.Regression.Backend.RationalPresentation \
  -norec PTree.Regression.Infrastructure.AllImports
```

Results:

- full build, including AllImports;
- 111 tool tests and architecture/report checks;
- exact source conservation, all 13 compiled client signatures/assumptions
  compared with the independently replayed frozen source;
- all 39 new constants closed under the global context;
- 505 existing exact compiled contracts and assumptions unchanged;
- soundness audit: 199 exact contracts, 36 generic quotient endpoints,
  18 finite-real joint endpoints, 80 native MathComp endpoints;
- seven-module joint `coqchk -norec`, including both native-transport clients.

The kernel command was run after the full build completed. It checks the
named module bodies while trusting their dependencies, not the entire library
recursively. The full build still includes the two unchanged Gate M modules;
it is not claimed wholly universe-checked. Those two modules are excluded from
the targeted kernel set. CI remains intentionally ignored; environment and
checker settings are unchanged.

Counts: 285 -> 287 theory modules; 76 -> 77 Regression modules; 283 -> 285
Gate S modules; 2 -> 2 Gate M modules. The new Common module contains 18
definitions/lemmas, and the regression contains 21 definitions/examples.

## Next boundary

This increment isolates the **representation portion** of finite presentation;
it does not claim the finite-transport or atom-mass migration is finished.
Scaling/bind and atom-mass algebra still need adaptation before switching
`EnumQ`/`SubEnumQ` to `FiniteEnum rat`/`FiniteSubdist rat`. Do not mark Phase 4
complete or remove `nnQ` on the strength of this checkpoint.
