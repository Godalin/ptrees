# Repository architecture and maintained contracts

The repository separates program reasoning from its external mathematical
validation. The generated [inventory](../tools/data/ARCHITECTURE_AUDIT.md) checks every
local dependency, not just a selection of entry points. The domain-soundness
theorems are described in [FreeOmega soundness](FREEOMEGA_SOUNDNESS.md).

## Ownership and dependency direction

| Layer | Responsibility | Restrictions |
| --- | --- | --- |
| `Core` | PTree syntax and combinators | Core only |
| `Prob/Interface` | Operations and explicit law capabilities | No tree or concrete-backend dependency |
| `Prob/FreeOmega` | Formal completion syntax, approximation, observation and quotient | Generic native carrier; no concrete backend |
| `Prob/FreeOmega/Validation` | Native-parametric external model and soundness | No concrete backend; only `StableHitting` may directly read generic PTree hitting, reexported by `Soundness` |
| `Prob/Backend/{Common,EnumQ,SubEnumQ,SubEnumR,MathComp}` | Arithmetic, native models and their specialized endpoints | Common has no native-carrier dependency; MathComp is independent of EnumQ/SubEnumQ |
| `Prob/Domain` | Independent continuous expectations and standard measure correspondence | Domain and mathematical libraries only |
| `Eq` | Stable hitting, `pstruct`, `pstrong`, canonical `peutt` and profile selection | No Semantics/Interp dependency |
| `Semantics` | Raw/head transitions, comparison bisimulation and MDP fragment | No Interp dependency |
| `Interp` | Structural and behavioral interpreter theory | May consume Eq and Semantics |
| `Execution` | Concrete closed-tree runner and lawful ITree target for generic `Core.fold` | Core/Execution only; no validating model |
| `Execution/Backend` | Concrete samplers and finite outcome calculations | No dependency on execution validation |
| `Execution/Validation` | Conditional replay probability laws and hitting correspondence | One-way consumer, never a runtime or ordinary reasoning dependency |
| Top-level `PTree / Eq / PTreeFacts` | Program / relation / reasoning aggregates | Direct owner exports; no concrete backend or validating model |
| `Examples` | Program proofs, supporting mathematics and counterexamples | No tests dependency; not formal library dependencies |
| `Examples/Validation`, `Examples/Counterexamples/Validation` | External-model mathematical examples | One-way validation, not reasoning dependencies |
| Root `tests/` (`PTree.Tests`) | Isolated imports, inference, rewrite and universe clients | Root build checks them; not installed library theory |

In Eq, Semantics and Interp, the `FreeOmega/` namespace fixes only
`MF := FreeOmega MN`; `Backend/` additionally fixes a native model. These
are different specializations. Generic layers cannot import either kind
of specialization, and canonical-model layers cannot import concrete ones.
EnumQ and SubEnumQ can reuse each other's realization facts: SubEnumQ is a
validated EnumQ carrier, not an unrelated implementation.

`Prob/Legacy` remains noncanonical weighted infrastructure. It is not an
alternative to the subprobability-validity contract. Its existing clients
are retained; no deletion follows merely from its name.

## Behavioral operation selection

`Eq/Canonical.CanonicalBehavior MN` selects the complete operation profile
`(MF, FI, MX, FO)`, not just a frontier carrier. Its four fields contain no
law capabilities and are not registered as capability instances. Law search
then runs against the selected operations. There is no generic blanket
`MN -> FreeOmega MN` registration.

Concrete `Eq/Backend` adapters select observable FreeOmega for SubEnumQ, SubEnumR and
the still-maintained weighted EnumQ backend. The explicit builder lives in
`Eq/FreeOmega/Canonical`; it is not an instance. Weighted EnumQ's route is not
a subprobability-validity claim.

Structural FreeOmega operations and laws remain mathematical constants, but
their ten instance registrations are local. Internal proof clients opt in
locally. `FreeOmegaMixedMeasure` remains a shared global operation because
it selects neither structural nor quotient equality.

The existing Gate M MathComp assembly selects the native self-frontier.
It imports `Eq/Canonical` through the ordinary Eq dependency direction;
the former Eq-to-API exception has been deleted. Safe modules still cannot
depend on Gate M, directly or transitively; no unchecked file has been added.

Raw `PEutt.peutt` remains generic. The public `≈ₚ` belongs to `PEuttNotations`
in `Eq/Canonical` and selects the complete default profile. `PStructNotations`
and `PStrongNotations` belong to their relation owners. `Eq/Bind` owns the single
heterogeneous `peutt_bind`, using probability-level bind/order compatibility,
directed cofinality and increasing-chain selection. FreeOmega and MathComp
provide these laws without duplicating PTree coinduction. The lower-level
`peutt_bind_cofinal` accepts explicit scheduling. See
[generic bind extraction](THEORY.md#bind-and-rewriting) and [public modules](ARCHITECTURE.md#program-facing-versus-expert-imports).
`Eq/Algebra` owns generic bind/fmap `Proper` proofs. Probability-level derived
AE facts live in `Prob`, not comparison semantics; see
[generic algebra](THEORY.md#bind-and-rewriting) for the capability surface and local
rewriting profiles, and [relational consumers](THEORY.md#structural-bridges-and-relational-limits)
for the proved structural bridges and their relational-limit premises.

Route uniqueness is project policy, not a theorem about uniqueness of arbitrary
typeclass instances. Selecting the right carrier alone is insufficient: structural
`free_omega_lift` and observable `free_omega_qlift` interpret equality differently.

## Three layers of probability reasoning

The architecture is fixed around the following distinction, not a stronger
unified probability interface:

| Layer | What it establishes | What it does not require or claim |
| --- | --- | --- |
| Generic behavioral theory | Native capabilities give `FreeOmega MN`, relational lifting, `pstrong`/`peutt`, stable hitting, bind and iter laws | No independent external model or external joint-existence premise |
| Generic external validation | A native interpretation into `OmegaVal` and its explicit mathematical links give modelability and `qlift -> oval_bidual` for modelable endpoints | No actual-joint existence conclusion; raw derivation intermediates need not be modelable |
| Concrete-model realization | A particular probability model discharges the hypotheses for actual external joints | Not a prerequisite for being a usable behavioral backend |

**Generic layer proves necessary relational semantics; concrete probability
models prove realization/completeness when required.** Here completeness means
recovering an external joint from suitable external constraints, with the
model's required support hypotheses. It does **not** mean completeness of the
syntactic `free_omega_qlift` relation.

`Prob/FreeOmega/Validation/{Model,Continuity,Observation,Relational,Quotient}`
owns the second layer; see [generic validation](FREEOMEGA_SOUNDNESS.md#3-quotient-and-relational-soundness).
The independent Domain and Common transport theorems can be shared by concrete
realizations; their application must not become a premise of behavioral theory.

`Validation/StableHitting.v` is the explicitly one-way PTree bridge: it may
read generic hitting definitions, but neither behavioral theory nor pure
model validation may depend on it. `Validation/Soundness.v` is the validation
entry point. Both Q/R adapters discharge the same native obligations without
depending on specialized completion validation or PTree; their Eq/Backend
stable-hitting corollaries give automatic modelability of arbitrary witnesses.

SubEnumQ's legacy external names are consolidated in `Compatibility.v`, whose
validation proofs delegate to the generic model. The four former external
validation modules have been removed. Q/R canonical countable-support and joint
clients transitively exclude Compatibility and scalar Upper modules. The latter
still serve native transport/internal realization and must not acquire external
model dependencies; they are not obsolete compatibility modules. SubEnumR
instantiates generic validation and
proves countable support and external joint realization in
`Prob/Backend/SubEnumR/FreeOmega/JointRealization.v`, alongside `Validation.v`
not in generic `Validation/Quotient.v`; see the
[finite-real realization account](FREEOMEGA_SOUNDNESS.md#7-optional-backend-specific-actual-joint-realization).
The two finite native backends therefore share the external countable transport
theorem without strengthening generic validation beyond bidual constraints.
MathComp's native joint witness theorem remains separate; no MathComp
completion backend is maintained.

The maintained complete probability pairs are `SubEnumQ / FreeOmega SubEnumQ`
and `SubEnumR R / FreeOmega (SubEnumR R)`. MathComp native discrete
kernel/measure mathematics remains checked normally. Its probability-backend dependency closure
excludes `Prob/FreeOmega`; the former combination alias and specialized
behavioral clients have been removed, without changing generic `MN`/`MF`.
`MathComp/NativeLaws.v` retains same-carrier kernel algebra, while
`tests/Imports/MathCompUniverse.v` records the recursive-frontier
failure with universe checking enabled. The separate, exact-allowlisted
`Eq/Backend/MathComp.v` and `tests/MathComp.v` use
`Local Unset Universe Checking.` for direct assembly/probes only (Gate M).
Every other module belongs to Gate S and must not import Gate M, even through
regressions or helpers. Safe `AllImports` excludes both Gate M modules; its
old all-module coverage rule is deliberately narrowed to all safe modules.
Gate M is not part of the public facades or normally checked theory.
See [MathComp scope and verification](BACKENDS.md#mathcomp-mathematics-and-assumptions). The earlier completion
removal and native-only checkpoints are retained in Git, not current guidance.

Do not introduce an `ExternalJointRealization` capability merely to package
these strengthening theorems. Reconsider only if an actual generic consumer
needs that premise, with explicit review of the dependency boundary.

### Three meanings often called “coupling”

| Preferred term | Code | Meaning |
| --- | --- | --- |
| Relational lifting | `sem_lift`, `free_omega_qlift` | A relation between measures/representations; an external joint is not part of the generic contract |
| Semantic joint witness | `semantic_coupling` | An explicit joint in the same semantic carrier, with graph-lifting marginal constraints and AE relational support |
| External joint realization | `oval_joint`, `oval_coupled` | An independent `OmegaVal` joint with bounded-test marginal equality and concentration on the relation; `oval_coupled` asserts its existence |

The internal witness does not by itself provide an independent model. Likewise,
`oval_bidual` gives bounded-test constraints, not a joint witness. Use these
qualified terms in reports and paper claims; “coupling soundness” alone does
not specify which bridge was proved.

## Program-facing versus expert imports

```coq
From PTree Require Import PTree.     (* syntax only *)
From PTree Require Import Eq.        (* relations and notations *)
From PTree Require Import PTreeFacts. (* usual reasoning theory *)
From PTree.Eq.Backend Require Import SubEnumQ. (* optional default profile *)
From PTree Require Import Semantics. (* curated comparison semantics *)
```

The three main entry points directly export their selected owning modules,
not a parallel layer of theorem aliases. Helpers in an exported module are
visible; that is intentional. No concrete backend, external validation or
auxiliary Eq/Internal module enters those dependency closures. `PTree` alone
does not load probability interfaces. `≈ₚ / ≈ₚ[RR]` denotes canonical behavior;
`≡ₚ` and `≃ₚ` remain stronger proof relations, not competing weak semantics.

Expert clients import actual owners. In particular, `Eq/PEutt` no longer
forwards `Eq/StableHittingRelation`, and the three SubEnumQ FreeOmega
UpperExpectation/UpperCoupling/UpperContinuity modules no longer forward
`Prob/Backend/SubEnumQ/Expectation`. The latter owns finite expectation,
AE extensionality and finite/countable-sup interchange. Its dependency
closure, and that of native `SubEnumQ/Domain`, exclude FreeOmega.

## External validation is one-way

Generic `Prob/FreeOmega/Validation` and explicitly classified concrete
validation adapters may connect the independent domain with FreeOmega or
PTree. In particular, Common/DomainTransport and
Common/CountableCoupling connect independent scalar transport to OmegaVal;
they are not ordinary mainline Common dependencies.

The transitive closures of Core/Eq/Semantics/Interp/Examples and the
public entry points exclude all validation modules. Explicit external
adapters such as `Eq/Backend/StableHittingDomainSubEnumQ` are validation owners,
not reasoning roots, despite their physical namespace.
The model validates reasoning infrastructure;
reasoning infrastructure does not assume its own validating model.
Interpretation's generic endpoints consume explicit model laws; see the
[current capability map](THEORY.md#model-obligations-at-a-glance) for model-specific obligations.

The same one-way boundary applies to `Execution/Validation/*`.
`UniformReplay` validates the existing rational ticket runner under a
history-conditional uniform entropy law; `SubEnumQ` connects it to hitting.
Neither is part of the executable sampler or a required backend capability.
The generic `Core.fold` owns the separate Vis-handler/Prob-sampler abstraction;
Runner is a concrete closed-tree execution backend, not a second probability
semantics. No fold/runner correspondence is asserted. See
[execution roles](EXECUTION.md).

## Internal proof facilities and tests

FiniteInternal is auxiliary proof infrastructure for well-founded internal
compression and related adequacy arguments. It is not part of the canonical
PTree semantics or public equivalence theory. The peutt/Interp/facade closure
does not use `Eq/Internal`; the final SubEnumQ domain-soundness proof does not
need it either. Nevertheless its independent execution/scheduling/coupling
contracts, Recovery and residual infrastructure remain maintained. This cleanup
does not delete them on the basis of zero clients or absence from one proof.

Shared mathematical samples now live with their examples. Domain-only model
examples remain independent from FreeOmega examples. `OmegaValMeasure`, invalid raw Lub,
cofinality/diagonal misuse, raw observation mass escape, countable matrix mass
escape, partial mass and large-universe tests are distinct contracts.
Internal proof examples live in `Examples/Internal`, and independent canonical
routing probes in `tests/ImportOrder`; see the
[content policy](ARCHITECTURE.md#examples-and-tests). Positive rewriting and
inference tests are not replaceable by declaration snapshots.
`tests/AllImports` covers every other Gate S module exactly once, in sorted order.
Both `theories/` and `tests/` are included in the root `dune build`.
The alternate universe representation is only a compilation probe, not another
maintained syntax. No top-level `Events` namespace is introduced; standard
effects should reuse ITree definitions.

## Examples and tests

There is no maintained `theories/Regression/` namespace. Reusable semantic laws
belong in their production owner; mathematical programs/counterexamples belong
in `Examples/`; import order, negative inference, universe and rewrite-syntax
probes belong in non-installed `tests/`. Delete wrappers that merely repeat an
existing endpoint without exercising a distinct boundary. Examples may not
import tests, and production theory may not import either.

The root `dune build` checks all those actual compilation contexts. One aggregate
cannot replace isolated negative imports or inference clients. `tests/AllImports`
loads every other Gate S module exactly once and merges their universe constraints;
it excludes Gate M. Internal examples do not promote auxiliary certificate
machinery into another public equality. Standard effects reuse ITree definitions;
there is no parallel top-level Events namespace.

The completed reclassification and its move ledger remain in Git at `2ba1855`.
Current verification commands belong only in [AUDITING](AUDITING.md); generated
ownership/dependencies live in [the machine inventory](../tools/data/ARCHITECTURE_AUDIT.md).
