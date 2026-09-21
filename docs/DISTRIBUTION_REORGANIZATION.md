# Discrete two-level distributions: implementation checkpoints

Baseline: `28ae229`. Local validation only; CI is deliberately out of scope.

`MN` supplies native discrete sampling; `MF` supplies stable frontiers. The
generic tree theory assumes neither `MF = MN` nor `MF = FreeOmega MN`.
The independent expectation domain validates representations; it is not a
third project-wide distribution parameter or another free probability syntax.

## Existing completion capabilities

`Regression/Backend/BackendCapabilities.v` now checks the following with an
arbitrary native carrier, in separately scoped capability contexts. These
are existing implementations, not newly assumed mathematical laws.

Every row below has native `SemanticMeasure`, `CoreLaws`, and `SemanticOmega`
operations available. **Native `SemanticOmegaLaws` and native `BindLaws` are
not prerequisites.** Availability of a native lub relation must not be
confused with completeness of that relation (finite native carriers need
not contain all countable limits).

| Completed capability | Additional native requirement |
| --- | --- |
| Core, order, omega, total properness, cofinality, mixed omega | none |
| Bind and mixed bind | AE lifting |
| Mixed unit | Dirac AE |
| Nested native sampling / mixed node bind | Bind AE exactness |
| Fubini | Coupling AE |
| Diagonal, omega AE, coupling AE | Coupling AE + countable AE |

Commutativity remains optional. This table records sufficient, compiled
dependency profiles, not a claim of mathematical minimality.

## Work sequence and boundaries

1. Freeze the generic capability probes and baseline validation.
2. Add native-parametric external validation with AE-sensitive sample/bind
   closure; preserve the existing internal `free_omega_denotes` name and meaning.
3. Connect the existing SubEnum interpretation without changing DS1--DS5
   statements or replacing the qlift proof through inadmissible intermediates.
4. Develop finite-real native distributions, reusing generic completion work.
5. Audit/prove MathComp direct `MN = MF` capabilities before claiming the
   remaining obstacle is universe-level. Ordinary bind, relational bind,
   omega completeness and coupling gluing are separate obligations.

No unsafe universe experiment is part of the trusted theory. No such
experiment has been introduced at this checkpoint. Existing soundness,
partial-mass and invalid-raw-lub regressions remain authoritative.

### Capability checkpoint validation

Full local `dune build` (including AllImports), architecture/API/source audits,
all 48 tool tests, and the 505-entry compiled signature/assumption snapshot
passed. A targeted `coqchk -norec` of BackendCapabilities passed; this is not
a new recursive whole-library kernel audit. No CI claim is made.

## Native-parametric external validation

`Prob/FreeOmega/Validation/Expectation.v` parameterizes the raw upper evaluator
by `native : forall X, MN X -> OmegaVal R X`. The external mathematical domain
is deliberately **OmegaVal-qualified**, not an arbitrary abstract `MF` and not
a newly added project-wide `Model` parameter. The ordinary generic PTree
interfaces are unchanged.

`free_omega_modelable` means the evaluator satisfies the independent
expectation laws; `free_omega_model_denotes` compares bounded tests. It is a
semantic validity condition, not an inductive all-subterms-valid certificate.
It does not redefine the internal `free_omega_denotes` observation relation.

The new layer proves bounds, structural bind interpretation, uniqueness and
properness of denotation, sample/bind/lub closure, AE sample/bind closure and
denotation, approximation soundness, cofinality, double-lub interchange and
diagonalization. The additional native bridges are separately scoped:

- AE rules require native AE support to preserve bounded expectations.
- Approximation/cofinality require native relational bounded-test inequalities.
- Plain bind/lub rules need neither of those bridges, native relational bind,
  nor native omega completeness.

Outside the AE support, kernels are totalized by a valid zero using explicit
classical selection. Invalid raw terms themselves do not thereby gain a model.
Double-lub interchange is not a claim that arbitrary native sampling commutes.

`SubEnum/FreeOmega/GenericValidation.v` proves the new specialized evaluator
is definitionally the old `free_omega_upper`; modelability is equivalent to
DS admissibility and both denotations agree. It supplies the AE/test bridges
from finite expectation facts. No frozen DS theorem or old proof is changed.
General qlift joint realization is still the existing SubEnum theorem; the
new generic approximation result must not be advertised as generic qlift
soundness. In particular, no new induction over qlift intermediates is used.

Regressions include a second, option-valued native interpretation, import
isolation, null-weight invalid branches, invalid alternation, unbounded
geometric support, proof-independent model values and large-universe results.

Validation of this checkpoint: full build/AllImports; architecture, API and
source contracts; all 49 tool tests; all 505 frozen compiled contracts;
18 new endpoint `Check`/`Print Assumptions` probes against the existing axiom
whitelist; joint `coqchk -norec` of the generic validation, SubEnum adapter and
regression. All passed locally. The frozen DS sources were not edited.

## Finite-real native checkpoint (partial backend profile)

`SubEnumR R A` is a finite list of **real** weights/values, with proofs of
nonnegative coefficients and mass at most one. Ret, zero and list-based bind
construct inhabitants; bind mass closure and ordinary monad equations are
proved. Equality compares real-valued finite expectations; lifting requires
an actual finite joint with both expectation marginals and supported relation.

The native `SemanticMeasure`, subprobability predicate/closure/carrier, Dirac
AE, countable AE, AE Kleisli and exact bind AE instances are proved. Its
independent expectation model proves monotone continuity by finite weighted
supremum interchange. Native AE and coupling test soundness are proved.
`SubEnumR/FreeOmega/Validation.v` is only a thin specialization of the same
generic validation used by SubEnum: no duplicated completion proof chain.

`RationalEmbedding.v` gives `SubEnum -> SubEnumR R`, preserving all finite
real expectations and ret/zero/bind equality. Existing `SubEnum` keeps its
name and API; it is the rational (`SubEnumQ`) backend in the proposal.
The only permitted native cross-family import is this explicit embedding.

**Not completed:** finite-real coupling composition/gluing, the full native
Core/Bind packages, and therefore the full canonical FreeOmega behavioral
capability profile over SubEnumR. No gluing/existence assumption was added
to make the capability table look complete. The independent completion
validity results do not imply those missing relational capabilities.

The regression constructs an actual `sqrt(1/2)`-weighted coin (no rational
conversion), checks its expectation/totality, bind validity, invalid raw
alternation, an invalid null branch accepted by AE closure, and a valid
formal limit. It does not claim to prove irrationality of the coefficient.

Finite-real checkpoint validation passed: full build/AllImports; 254-module
architecture/source checks; API surface; all 49 tool tests; unchanged 505
compiled contracts; 13 new endpoint assumption probes; targeted joint
`coqchk -norec` of all six new modules. No CI was inspected or changed.
