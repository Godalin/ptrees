# Shared finite representation — Phase 2

Accepted starting point: `2f3889a` (Phase 0–1 naming migration).
This is an additive common-algebra gate, **not a backend migration**.
The [overall plan](FINITE_BACKEND_CONSOLIDATION.md) and Phase 1 source audit
are preserved unchanged; their historical naming-only claims are not relaxed.

## Representation and scalar boundary

`Prob/Backend/Common/FiniteEnum.v` defines a nonnegative weighting:

```coq
Record FiniteEnum (A : Type) := {
  finite_enum_raw : list (R * A);
  finite_enum_nonnegative : finite_nonnegative finite_enum_raw
}.
```

Here `R : numDomainType`, and `finite_nonnegative` means that every coefficient
occurring in the list is nonnegative. This is an ordinary-scalar list, not a
list of a nonnegative scalar subtype. Values may repeat; zero-weight entries
are retained. The result carrier is arbitrary `Type`, without equality,
inhabitation, finiteness or countability constraints.

`Prob/Backend/Common/FiniteSubdist.v` adds the independent mass refinement:

```coq
Record FiniteSubdist (A : Type) := {
  finite_subdist_enum : FiniteEnum R A;
  finite_subdist_mass_bound : finite_mass finite_subdist_enum <= 1
}.
```

Both invariants inhabit `Prop`. The intended runtime representation is an
ordinary weighted list after proof erasure; this gate does not claim an
extraction benchmark or executable implementation of arbitrary real scalars.

Only an ordered integral-domain structure is used: no division, completeness,
`realType`, classical probability capability or `SemanticMeasure` is required
by the common theory. Both MathComp rational and real scalars instantiate it.
No new class, axiom, scalar subtype or semantic equivalence is introduced.

## Algebra and API

The raw-list layer exposes `finite_expect f raw`, `finite_weight_map` (scaling
all weights by one scalar) and `finite_bind`. Raw expectation is algebra on
lists, not an assertion that a list represents a probability distribution.

The invariant-carrying layer exposes:

```text
finite_enum_of_list       custom raw list + sign proof
finite_enum_ret / zero    constructors with automatic sign proofs
finite_enum_scale        nonnegative scaling (no mass restriction)
finite_enum_map           map values, preserving weights
finite_enum_bind          multiply and flatten finite weightings
finite_enum_expect mu f   expectation on a checked weighting
finite_mass mu            expectation of the constant one function

finite_subdist_of_list    custom raw list + sign proof + mass proof
finite_subdist_ret / zero / map / bind
finite_subdist_scale      scaling by a coefficient in [0,1]
finite_subdist_expect mu f
```

All constructors are transparent `Defined` terms. Ordinary bind clients
automatically obtain nonnegativity and mass <= 1, without supplying new
proof fields. `finite_weight_map` is same-scalar scaling, **not** the generic
Q-to-R scalar conversion reserved for Phase 6.

Proved raw-list laws cover extensionality, zero/add/scale/append, value-map,
weight scaling, bind expectation, monotonicity, nonnegativity, and AE
monotonicity/extensionality ignoring zero-weight entries. Checked-operation
laws cover ret/zero/map/scale/bind expectations and their mass formulas.
Subdistribution bind left/right unit and associativity are stated on
expectations, not record equality; no proof irrelevance or new quotient is
needed.

## Regression boundaries

`Regression/Probability/FiniteRepresentation.v` checks:

- A weighting containing two copies of `true` and a zero-weight `false`
  retains the raw list and has mass 2. It cannot become a subdistribution.
- A negative coefficient fails the sign invariant. Missing sign/mass
  certificates are rejected by `Fail Definition` probes.
- Zero-weight branches do not affect expectations, including the AE rule.
- Arbitrary bind preserves both sign and mass constraints and satisfies
  the expectation formula.
- Zero is available on an empty result carrier.
- Ordinary rational half-mass sampling binds to quarter mass.
- A real `sqrt(1/2)` coefficient uses the same representation with no rational
  encoding. The regression does not prove that coefficient irrational.
- A carrier containing `Type@{u}` supports ret and bind with normal universe
  checking.
- Importing the common layer does not load probability interfaces, PTree,
  FreeOmega, OmegaVal, `nnQ`, SubEnumQ or SubEnumR.

## Preservation and audits

`tools/audit_finite_representation.py` compares against the frozen `2f3889a`
git archive. All 276 old `.v` modules remain byte-identical except the three
sorted imports added to AllImports. The only three new theory modules are
the two common modules and their regression.

Existing snapshots, theorem statements, proofs, public facades, audit tools,
trust policies and backend representations are unchanged. The old contract
policy may only gain the new regression's 18 theorem names; the generated
architecture inventory is checked against the actual dependency graph.
No old module outside AllImports may import any of the new modules.

This is a Phase 2 preservation gate, not a restriction on the subsequently
authorized Phase 3 migration. The old Phase 1 check is intentionally not run
against this larger source tree: it remains the exact check for its own
frozen checkpoint, and has not been weakened.

Counts: 279 theory modules (277 Gate S / 2 Gate M), 72 regression modules,
4101 direct local Require edges, 16 Python tool files and 82 tool tests.
The original 505-entry compiled snapshot is unchanged, not regenerated.

Local checks completed:

- Full `dune build`, including the safe AllImports aggregate.
- Exact Phase 2 source conservation and independent common-layer boundary.
- All 505 exact compiled contracts and per-endpoint logical assumptions.
- Architecture ownership/dependency checks and curated API surface checks.
- All 82 Python tool tests, including mutation tests for source conservation,
  import isolation and accidental logical assumptions in the shared algebra.
- Long-term soundness audit: 199 frozen exact contracts, 36 generic
  validation, 18 finite-real realization and 80 native MathComp endpoints;
  unchanged logical whitelist and no unfinished proof/capability drift.
- New compiled audit: 52 common declarations are closed under the global
  context. The 23 regression declarations stay within the existing logical
  whitelist; real square-root facts inherit MathComp's propositional and
  dependent functional extensionality and constructive indefinite description.
- Joint targeted `coqchk` for FiniteEnum, FiniteSubdist, FiniteRepresentation
  and AllImports. `-norec` checks these module bodies while trusting compiled
  dependencies; this is not a recursive whole-library audit. Gate M is absent.

Verification commands:

```sh
opam exec -- dune build
python3 tools/audit_finite_representation.py
python3 tools/audit_architecture.py --check
python3 tools/audit_api.py --check --surface-only
python3 tools/audit_assumptions.py --check
python3 tools/audit_soundness.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Prob.Backend.Common.FiniteEnum \
  -norec PTree.Prob.Backend.Common.FiniteSubdist \
  -norec PTree.Regression.Probability.FiniteRepresentation \
  -norec PTree.Regression.Infrastructure.AllImports
```

CI and environment changes remain out of scope. Neither MathComp theory nor
its two-file Gate M universe relaxation is changed or extended.

## Stop point

Phase 2 makes the future shared records available, but **EnumQ, SubEnumQ and
SubEnumR still use their accepted existing representations**. No old finite
algebra has been removed yet. No maintained `nnQ` dependency has been removed
or deprecated prematurely. Phase 3 is the separate SubEnumR migration gate;
the rational migration, generic scalar transport and deduplication follow it.
