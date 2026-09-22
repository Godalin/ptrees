# Finite backend consolidation: final migration

## Outcome

The proposal's Phases 0–7 are implemented. This final increment is based on
`1cba6c5`, following the accepted finite-presentation checkpoint `8610c68`
and the shared algebra/scalar-transport and support increments `f9485be` and
`1cba6c5`. It performs the production rational carrier switch and migrates
all its clients. It does not change the environment or investigate CI.

```text
EnumQ A       := FiniteEnum rat A
SubEnumQ A    := FiniteSubdist rat A
SubEnumR R A  := FiniteSubdist R A
```

All three are literal specializations of the shared records, not an old/new
representation conversion pipeline. Ordinary coefficients remain in the raw
list. Nonnegativity belongs to the container; the subdistribution record adds
the mass bound. Order, duplicate entries and zero-weight positions are retained.

The maintained configurations remain SubEnumQ/FreeOmega SubEnumQ,
SubEnumR/FreeOmega SubEnumR, and direct MathComp with MN = MF. The finite
records have not been made omega-complete.

## Implementation and client changes

- Shared finite operations, expectation, atoms, support, positions, pruning,
  presentation, indexed-bind positions and scalar transport are reused.
  Coupling/equality remain backend-owned mathematics.
- `subenumQ_to_R` now uses `finite_subdist_map_weights` with `ratr` and its
  order proof. The previous nnQ/Qval route is gone from production.
- `nnQ` and its existing HB support are retained in
  `Prob/Legacy/RatSubTypes.v`. The old discrete classes needed by legacy code
  reside in `Prob/Legacy/RationalDiscrete.v`. Native finite backends and
  Examples cannot import this legacy layer.
- The old/shared correspondence is retained only as a historical regression
  fixture. Production does not import it or use restore/repack helpers.
- Rational constructors with arbitrary weights now take ordinary `rat`
  values and explicit nonnegativity proofs. Former nnQ parameters in example
  theorems become a rational parameter plus its existing invariant, not an
  additional mathematical restriction.
- List consumers use explicit projections. `enumQ_raw` returns the list;
  `subenumQ_raw` returns a checked EnumQ; `subenumQ_data` returns the list.
  There is no silent coercion from a checked carrier to an unchecked list.
- Raw-data equality is used for finite algebra. Optional exact record
  equality for observation-witness clients is provided by
  `FiniteRecordExtensionality.v`: functional extensionality and Boolean UIP
  suffice. No general proof-irrelevance axiom is added, and native algebra or
  instances do not import that optional module.

Indexed coupling still compares actual finite joint marginals and supported
related entries. Rational semantic equality still uses indexed coupling after
zero pruning; it has not been replaced by a different relation. AE still
ignores precisely zero-weight entries. RandomWalk, Bernoulli factories,
interactive Von Neumann, the strictness examples, native validation and joint
soundness all compile with the new carriers.

## Preservation evidence

`tools/audit_finite_consolidation.py` deliberately replaces, rather than
weakens, the historical phase-specific source audits.

- 125 generic/interface/domain/MathComp/real-backend source modules are
  byte-for-byte unchanged against `1cba6c5`. The explicit exceptions are the
  rational cofinality client, rational MDP embedding client and Q-to-R adapter.
- All 505 frozen compiled endpoint signatures are preserved after explicit
  owner relocation and definitional `rat`-projection normalization. No premise
  is removed by normalization. Of the snapshot entries, 411 remain identical;
  94 reflect printing/owner changes or the assumption reduction below.
- No frozen endpoint gains a logical assumption. The rational unlabelled MDP
  endpoint drops its former sole functional-extensionality dependency.
  Same-name logical assumptions are compared by their declarations as well.
- The snapshot was refreshed only after comparing fresh compiled results with
  the frozen baseline. This is not an unrestricted baseline recapture.
- A further 169 shared-helper/new-regression endpoints are checked: shared
  algebra is closed; the optional exact-record helper is allowed only the
  existing functional-extensionality axiom; three realType regression endpoints
  inherit the established MathComp extensionality/choice assumptions.
- Architecture rejects native finite-backend imports of Legacy. Source checks
  reject nnQ/Qval and old/shared runtime conversions in the maintained finite
  backends and Examples. Mutation tests cover the contract comparison.

This does not claim that every representation-specific lemma kept its old
syntactic type: scalar proof parameters and explicit raw projections necessarily
change those APIs. Frozen semantic/public endpoints retain their strength, and
the complete client rebuild checks the migrated implementation.

## Local validation

The following completed successfully:

```sh
opam exec -- dune build
python3 tools/audit_finite_consolidation.py
python3 tools/audit_architecture.py --check
python3 tools/audit_api.py --check
python3 tools/audit_assumptions.py --check
python3 tools/audit_soundness.py --check
python3 tools/audit_mathcomp_direct.py --gate M
python3 -m unittest discover -s tools -p 'test_*.py'
git diff --check
```

The migration's 505-contract check and its 169-helper check were also run
independently while reviewing the snapshot. Results:

- Full build including AllImports: passed.
- 123 Python tests: passed.
- 306 API/helper contracts and 25 capability contracts: covered and checked.
- 505 current compiled contracts: exact snapshot check passed.
- Soundness: 199 frozen contracts, 36 generic validation endpoints,
  18 finite-real realization endpoints and 80 native MathComp endpoints passed.
- Gate M: 30 direct endpoints and 6 safe controls retain their types, logical
  assumptions and unsafe-hierarchy reports. Its two source files are unchanged.

A single targeted joint kernel check passed with `coqchk -silent`,
`-R _build/default/theories PTree` and **a separate `-norec` before every module**:

```text
Prob.Backend.Common.{FiniteEnum,FiniteSubdist,FiniteIndexedBind,
                    FiniteScalarMap,FiniteRecordExtensionality}
Prob.Backend.EnumQ.{Representation,Coupling,IndexedCoupling,FrontierLift,
                   Measure,FinitePresentation,Disintegration}
Prob.Backend.EnumQ.FreeOmega.NativeTransport
Prob.Backend.SubEnumQ.{Representation,Measure,Expectation}
Prob.Backend.SubEnumQ.FreeOmega.JointSoundness
Prob.Backend.SubEnumR.RationalEmbedding
Eq.Backend.StableHittingDomainSubEnumQ
Regression.Backend.FiniteBackendConsolidation
Examples.RandomWalk
Examples.MixedHeadProtocol
Examples.BernoulliFactory.BernoulliFactoryComposition
Examples.InteractiveVonNeumann.InteractiveVonNeumannService
```

These are 24 safe module bodies, with compiled dependencies trusted. This is
**not** a recursive whole-library kernel audit. Neither Gate M module is in
that check. Ordinary full build includes Gate M and must not be described as
an entirely universe-checked build. No remote CI result is claimed.

## Size and completion boundary

| Checkpoint | Theory modules | Regression modules |
| --- | ---: | ---: |
| Accepted `8610c68` | 287 | 77 |
| Pre-switch `1cba6c5` | 293 | 79 |
| Final migration | 298 | 80 |

The final graph has 4,216 direct local import edges, 296 Gate S modules and
the same two Gate M modules. `nnQ` deletion is not required by the proposal;
its isolated legacy retention is intentional. No new semantic capability,
axiom, probability model or checker bypass has been introduced. Further
coupling genericization, legacy deletion and MathComp redesign are outside
this completed consolidation.
