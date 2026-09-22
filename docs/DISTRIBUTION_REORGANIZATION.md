# Discrete two-level distributions: implementation checkpoints

Current scope supersedes the earlier work sequence below: the fully
universe-checked PTree probability pairs are SubEnum/FreeOmega and
SubEnumR/FreeOmega. MathComp's direct pair `MN = MF = MathCompKernelMeasure R`
is complete under the accepted Gate M trust boundary at `5dac49a`, with
coupling composition still conditional on `MathCompCouplingGluing`.
Native order, omega, continuity, diagonal/Fubini and relational bind are
proved with normal checking; only direct recursive-frontier assembly and its
regression use the two-file universe bypass. The checked negative universe
regression remains. MathComp + FreeOmega stays deleted; see
[MathComp direct status](MATHCOMP_DIRECT.md).

Follow-up: [SubEnumR behavioral backend](SUBENUMR_BEHAVIORAL_BACKEND.md)
completes the native relational laws and checks generic FreeOmega/PTree
assembly. The partial SubEnumR status below records the earlier `7e75db0`
checkpoint, not the current capability boundary.

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

## Historical work sequence and boundaries

1. Freeze the generic capability probes and baseline validation.
2. Add native-parametric external validation with AE-sensitive sample/bind
   closure; preserve the existing internal `free_omega_denotes` name and meaning.
3. Connect the existing SubEnum interpretation without changing DS1--DS5
   statements or replacing the qlift proof through inadmissible intermediates.
4. Develop finite-real native distributions, reusing generic completion work.
5. At the removal checkpoint, the MathComp self-model investigation was closed:
   retain native mathematics, not a third PTree behavioral backend. Ordinary
   bind, relational bind and omega completeness remain distinct mathematical
   properties; no new proofs of them are part of this removal.

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

## MathComp same-carrier investigation and accepted outcome

The investigation's useful results now live in `MathComp/NativeLaws.v`, at
the native carrier universe. They include actual mixed-bind operations, mixed
unit, mixed node-bind flattening, total properness and zero-prefix/constant
chain cofinality instances, without a gluing context. It also proves
returned-event zero, order reflexivity/transitivity/bottom and continuation
bind monotonicity. Ordinary native monad equations already existed; these
instances reuse them. At that checkpoint no full relational bind instance
was claimed; `BindLaws.v` now supplies it by an actual joint-kernel construction.

The original investigation separated mathematical gaps from the universe
boundary. The mathematical gaps are now closed; current status at `5dac49a`:

| Obligation | Current status |
| --- | --- |
| Ordinary bind and same-carrier mixed operation | proved |
| Mixed unit / nested native flattening | proved, no gluing premise |
| Foundational native AE | pre-existing |
| Total properness / zero-prefix and constant lub | proved |
| Full order package (including source-measure bind monotonicity) | proved in checked `OrderLaws.v` |
| Increasing-chain limit existence and bind continuity | proved in checked `OmegaLaws.v` |
| Diagonal / Fubini capability packages | proved from the same diagonal cofinality theorem |
| Coupling composition | existing explicit `MathCompCouplingGluing` assumption |
| Relational kernel bind | proved in checked `BindLaws.v`, without gluing |
| Recursive PTree frontier, hitting existence and eventful bind | available only in isolated Gate M; not a universe-checked instantiation |

### Historical integration finding and retained checked boundary

A standalone file could typecheck the canonical PTree head type,
its same-MathComp frontier, primitive kernel and `peutt` definition. This
is **not** sufficient evidence for a self-model: importing its compiled
module into AllImports failed with a universe inconsistency.

Dependency reduction found that one existing module,
`Regression/Backend/FreeOmegaUpperContracts`, suffices to reproduce the
conflict. With that module loaded first, a native PTree and its stable head
still typecheck, but applying the sealed MathComp carrier to that head is
rejected: the required strict inequality conflicts with
`MathCompKernelMeasure.u0 = PTree.Core.PTreeDefinition.61`.
The primitive kernel and `peutt` instantiations fail as well.

`Regression/Infrastructure/MathCompUniverse.v` preserves these as checked `Fail`
commands with positive tree/head controls and actual safe capability tests.
The failure was independently inspected without `Fail`: it is a universe
inconsistency, not a missing identifier or incorrectly supplied argument.
The standalone positive instantiations are not retained as jointly usable
trusted results.

That checkpoint added no `Unset Universe Checking` experiment. The later
Gate M policy explicitly permits it in exactly two direct-client files;
the independent omega/relational-bind mathematics was proved normally, not
discharged by the bypass. The negative probes above continue to document
why Gate M is not a normally universe-checked backend.

The MathComp carriers here are fully discrete/powerset measurable carriers.
This is not a continuous/Gaussian/Borel backend, and discreteness alone is
not a countable-support certificate.

## Convergence and next work

The original completed checkpoints were: generic capability inventory; native-parametric
OmegaVal validation; unchanged SubEnum DS bridge; finite-real representation,
ordinary/AE laws, native model and Q-to-R embedding; safe partial MathComp
same-carrier capabilities and a reproducible joint-universe boundary.

The real-weight regression additionally constructs a genuinely unbounded
retry chain using the square-root-weight coin. Increasing approximants and
validity of their lub use the generic completion proof, with no rational
conversion and no assumption of eventual stabilization. This is validity,
not yet a theorem computing its termination probability.

Subsequent work completed finite-real native relational laws, the full generic
behavioral profile, generic bidual validation and concrete SubEnumR external
joint realization. Coupling soundness is closed for the two maintained finite
native backends. Arbitrary-native actual-joint existence is not a current goal.
Direct MathComp theory is now accepted at `5dac49a` under the separate Gate M
trust boundary described above. Native MathComp analysis stays checked
independently; do not reintroduce the deleted completion path. This theory
round is closed; further probability infrastructure is not a follow-up goal.

The original checkpoint did not change public facades, add semantic classes
or transport-existence axioms, upgrade the environment, work on remote CI,
or clean up retained internal infrastructure. Native weighted lists and their
validity record were the new representation; the only formal completion is FreeOmega.

## Review checkpoints

| Commit | Purpose |
| --- | --- |
| `55b6809` | Compile existing FreeOmega capabilities over arbitrary MN, with separately scoped prerequisites |
| `efa262e` | Generic OmegaVal validation, AE closure, limit algebra and unchanged SubEnum DS bridge |
| `d0b2411` | Finite-real native distributions, ordinary/AE laws, external model and Q-to-R embedding |
| `c970eea` | Genuinely unbounded real-weight retry, using the generic validity/lub theory |
| Original MathComp checkpoint | Safe same-carrier laws and reproducible joint-universe boundary |
| `5dac49a` (accepted follow-up) | Checked native omega/relational bind and complete Gate M direct behavioral backend, with explicit gluing premise |

The validation record below is for the original checkpoint, not `5dac49a`.
Current verification scope and results are recorded in [MathComp direct status](MATHCOMP_DIRECT.md).

All old formal theory/proof files were compared byte-for-byte with `28ae229`.
Only two old `.v` files changed: the capability regression gained generic
probes and AllImports gained sorted imports. DS1--DS5, public facades,
FreeOmega syntax/quotient and all existing theorem statements/proofs stayed
unchanged. Modules: 245 -> 256; regression modules: 62 -> 65.

The existing 505 compiled signatures and per-endpoint logical assumptions
remain exactly unchanged. Another 38 new endpoint probes were checked against
the existing logical-axiom whitelist; all passed. New MathComp safe endpoints
do not require `MathCompCouplingGluing`. Generic AE/test-soundness bridge
premises are explicit parameters, discharged for both rational and real
finite backends, not new axioms or a new typeclass hierarchy.

The final source audit also rejects `Unset Universe Checking` in maintained
theory. Build/AllImports, architecture, API, source checks and all 50 tool
tests passed. The final joint `coqchk -silent -norec` of all 11 added formal
modules passed (exit status 0), in addition to the earlier targeted checks.
This checks those modules together; it is not a recursive whole-library
kernel audit. No remote-CI success is claimed by these checks.
