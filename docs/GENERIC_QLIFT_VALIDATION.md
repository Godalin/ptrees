# Native-parametric bounded-test validation

Baseline: accepted `c223393` (finite-real native coupling and the generic
FreeOmega behavioral profile). This follow-up extracts the next layer only:

```text
raw free_omega_qlift T t u
              ↓
bounded-test inequalities in BOTH directions
              ↓  only when the endpoints are modelable
oval_bidual T (model t) (model u)
```

This is **not** a generic actual-joint realization theorem. The existing
SubEnum DS1–DS5 results, definitions, proofs and public APIs are unchanged.
No MathComp self-model work, new completion, or new capability class is added.

## Interpretation obligations, not new probability axioms

The generic theorem takes `native : forall X, MN X -> OmegaVal R X`, native
`SemanticMeasureCoreLaws`, `SemanticOmega` operations, and six proved links:

| Link | Required meaning |
| --- | --- |
| AE | Native almost-everywhere support implies domain concentration. |
| ret | Native return denotes the domain Dirac value. |
| zero | Native zero denotes domain bottom. |
| bind | Native bind denotes domain bind on bounded tests. |
| lift | Native relational lifting implies bounded-test inequalities. |
| lub | Given an increasing interpreted native chain and a native `sem_lub` witness, its expectation is the scalar supremum. |

There is **no** native `SemanticOmegaLaws`/omega-completeness premise, native
`SemanticMeasureBindLaws` premise, or external-joint-existence premise.
The six links are ordinary explicit theorem arguments. Both concrete
adapters discharge every one of them, without leaving a model capability
for callers to assume.

`SubEnum/FreeOmega/RelationalValidation.v` uses its existing finite expectation
theory and scalar monotone-convergence lemma. The latter is still owned by
the frozen `UpperObservation` module; no native `Domain -> FreeOmega` edge is
introduced. It does not use old quotient soundness to prove the new bridge.

`SubEnumR/FreeOmega/RelationalValidation.v` uses the finite-real interpretation
laws and its existing native pointwise least-upper-bound predicate. Neither
adapter repeats the FreeOmega quotient induction.

## Proof layers

- `Validation/Continuity.v`: monotonicity and continuity of raw upper
  evaluators on increasing bounded tests; AE-only sample/lub interchange;
  bind/diagonal interchange. Raw terms need not be additive.
- `Validation/Observation.v`: native-parametric correctness of
  `free_omega_observes`, including the increasing-lub constructor.
- `Validation/Relational.v`: bounded fiber envelopes, relation composition,
  support restriction, bind and sample. These are validation predicates,
  not additional PTree behavioral equivalences.
- `Validation/Quotient.v`: all raw qlift constructors, carrying both
  directions rather than deriving symmetry by invalid complement algebra.

The main endpoint is `model_qlift_bidual_raw`. Its `FOQLComp` case interpolates
a bounded test through the relation's fibers. It does not interpret the
middle term as a measure and does not require middle-term modelability.
Induction here is on **raw scalar constraints**, not a joint realization
induction that would require legal probability objects at every intermediate.

Derived endpoints are `model_qlift_bidual`, `model_qlift_upper_mass`,
`model_qlift_eq_upper`, `model_qlift_eq_modelable` and `model_qlift_eq_sound`.
Equality transports validity and yields `oval_eq`; arbitrary relations yield
dual constraints only. No joint/completeness claim is made.

## Regression contracts

`Regression/Probability/GenericQuotientValidation.v` checks:

- no concrete backend or PTree is loaded by the generic bridge;
- an explicit heterogeneous `FOQLComp` through the already-proved invalid
  real alternating term, with valid endpoints;
- raw reflexive qlift does not certify validity;
- bottom cannot be quotient-equal to a unit-mass return;
- non-diagonal real-weight sampling, with `sqrt(1/2)` used as a real
  coefficient (no claim that the regression proves irrationality);
- duplicate/zero entries at half mass, without normalization;
- native observation of a genuinely increasing raw lub;
- `FOQLSampleLub` with a non-monotone chain on a zero-mass branch;
- validity transported across a quotient equality of an unbounded retry;
- independently quantified high-universe result carriers;
- the rational specialization agrees with the frozen DS5 test constraints.

## Reproducible checks

Use the existing local opam environment; CI is deliberately out of scope.

```sh
opam exec -- dune build
python3 tools/audit_architecture.py --check
python3 tools/audit_api.py --check --surface-only
python3 tools/audit_soundness.py --check --generic-quotient-only
python3 tools/audit_assumptions.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
```

The generic-quotient audit queries compiled types and `Print Assumptions`
for the new generic endpoints, both adapters and the regression contracts.
It retains the existing logical-axiom whitelist and separately rejects a
concrete native carrier, native omega-completeness or native relational-bind
law in generic endpoint signatures. The 505 frozen contracts are not
regenerated. New files remain in the one-way validation layer: the maintained
PTree reasoning infrastructure cannot depend on these external models.

## Verification result

- Full local `dune build`, including AllImports: passed, 267 modules.
- Architecture, public API and source-safety contracts: passed.
- All 52 tool tests: passed.
- All 505 frozen compiled signatures and per-endpoint assumptions: unchanged.
- All 36 new generic/adapter/regression endpoints: checked with the existing
  logical-axiom whitelist, without widening it.
- Joint `coqchk -silent -norec` of the four new generic modules, the two
  concrete adapters and the new regression: passed. This is a **targeted**
  seven-module kernel check, not a recursive whole-library audit.

Among pre-existing `.v` files, only AllImports changes (seven additional
imports). Existing DS1–DS5, native laws, FreeOmega definitions and maintained
PTree proofs are untouched. No `Admitted`, new axiom/class, unsafe universe
setting, environment update or CI change was introduced.
