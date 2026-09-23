# Repository architecture and maintained contracts

The repository separates program reasoning from its external mathematical
validation. The generated [inventory](ARCHITECTURE_AUDIT.md) checks every
local dependency, not just a selection of entry points. The domain-soundness
theorems are described in [FreeOmega soundness](FREEOMEGA_SOUNDNESS.md).

## Ownership and dependency direction

| Layer | Responsibility | Restrictions |
| --- | --- | --- |
| `Core` | PTree syntax and combinators | Core only |
| `Prob/Interface` | Operations and explicit law capabilities | No tree or concrete-backend dependency |
| `Prob/FreeOmega` | Formal completion syntax, approximation, observation and quotient | Generic native carrier; no concrete backend |
| `Prob/FreeOmega/Validation` | Native-parametric external bounded-test validation | May consume Domain and generic FreeOmega; no concrete backend |
| `Prob/Backend/{Common,EnumQ,SubEnumQ,SubEnumR,MathComp}` | Arithmetic, native models and their specialized endpoints | Common has no native-carrier dependency; MathComp is independent of EnumQ/SubEnumQ |
| `Prob/Domain` | Independent continuous expectations and standard measure correspondence | Domain and mathematical libraries only |
| `Eq` | Stable hitting, `pstruct`, `pstrong`, canonical `peutt` and profile selection | No Semantics/Interp dependency |
| `Semantics` | Raw/head transitions, comparison bisimulation and MDP fragment | No Interp dependency |
| `Interp` | Structural and behavioral interpreter theory | May consume Eq and Semantics |
| Top-level `PTree / Eq / PTreeFacts` | Program / relation / reasoning aggregates | Direct owner exports; no concrete backend or validating model |
| `Examples` | Applications and program proofs | No Regression dependency |
| `Regression` | Positive, negative, integration and capability tests | Not formal library dependencies |

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

The existing Gate M direct MathComp assembly selects the native self-frontier.
It imports `Eq/Canonical` through the ordinary Eq dependency direction;
the former Eq-to-API exception has been deleted. Safe modules still cannot
depend on Gate M, directly or transitively; no unchecked file has been added.

Raw `PEutt.peutt` remains generic. The public `≈ₚ` belongs to `PEuttNotations`
in `Eq/Canonical` and selects the complete default profile. `PStructNotations`
and `PStrongNotations` belong to their relation owners. The generic bind theorem
is named `peutt_bind_cofinal`; only the unconditional observable FreeOmega
corollary is named `peutt_bind`. See [public modules](PUBLIC_MODULES.md).

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

`Prob/FreeOmega/Validation/{Expectation,Continuity,Observation,Relational,Quotient}`
owns the second layer; see [generic validation](GENERIC_QLIFT_VALIDATION.md).
The independent Domain and Common transport theorems can be shared by concrete
realizations; their application must not become a premise of behavioral theory.

SubEnumQ's frozen DS1–DS4 account supplies denotational validation, and DS5
supplies backend-specific external joint realization. Keep those existing
owners and theorem names. SubEnumR instantiates generic validation and now
proves countable support and external joint realization in
`Prob/Backend/SubEnumR/FreeOmega/JointRealization.v`, alongside `Validation.v`
and `RelationalValidation.v`, not in generic `Validation/Quotient.v`; see the
[finite-real realization account](SUBENUMR_JOINT_REALIZATION.md).
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
`Regression/Infrastructure/MathCompUniverse.v` records the recursive-frontier
failure with universe checking enabled. The separate, exact-allowlisted
`Eq/Backend/MathComp/Direct.v` and `Regression/Backend/MathCompDirect.v` use
`Local Unset Universe Checking.` for direct assembly/probes only (Gate M).
Every other module belongs to Gate S and must not import Gate M, even through
regressions or helpers. Safe `AllImports` excludes both Gate M modules; its
old all-module coverage rule is deliberately narrowed to all safe modules.
Gate M is not part of the public facades or normally checked theory.
See [direct scope and verification](MATHCOMP_DIRECT.md) and the historical
[completion-removal record](MATHCOMP_NATIVE_SCOPE.md).

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
Interpretation remains FreeOmega-qualified, not a claim about arbitrary MF.

## Internal proof facilities and tests

FiniteInternal is auxiliary proof infrastructure for well-founded internal
compression and related adequacy arguments. It is not part of the canonical
PTree semantics or public equivalence theory. The peutt/Interp/facade closure
does not use `Eq/Internal`; the final SubEnumQ domain-soundness proof does not
need it either. Nevertheless its independent execution/scheduling/coupling
contracts, Recovery and residual infrastructure remain maintained. This cleanup
does not delete them on the basis of zero clients or absence from one proof.

`Regression/Fixtures` contains private shared samples, not final endpoint
tests; it cannot depend on the other Regression families. Domain-only tests
remain independent from FreeOmega tests. `OmegaValMeasure`, invalid raw Lub,
cofinality/diagonal misuse, raw observation mass escape, countable matrix mass
escape, partial mass and large-universe tests are distinct contracts.
`AllImports` covers every other module exactly once, in sorted order.
The alternate universe representation is only a regression, not another
maintained syntax. No top-level `Events` namespace is introduced; standard
effects should reuse ITree definitions.

## Stable audit commands

```sh
python3 tools/audit_architecture.py --aggregate-only
opam exec -- dune build
python3 tools/audit_architecture.py --check
python3 tools/audit_api.py --surface-only
python3 tools/audit_soundness.py --source-only
python3 tools/audit_assumptions.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
python3 tools/audit_api.py --surface-only --kernel
```

`CONTRACTS.json` stores full compiled types and per-endpoint `Print Assumptions`
for 266 distinct owner/helper endpoints (including the original 25 capability probes)
and 199 soundness endpoints. It is not a list of class counts or a claim of
mathematical minimality. `CONTRACT_POLICY.json` fixes existing class bodies,
curated facade text and named regression coverage. The audits are read-only;
changing a contract requires explicit review, not automatic regeneration.

The [printed-contract CI profile](../.github/ci/README.md) fixes OCaml 5.2.1,
Dune 3.17.2 and all 67 recorded dependency versions, including
Coq 8.20.1, HB 1.8.1, Coq-Elpi 2.4.0,
ExtLib 0.13.0, ITree 5.2.1, coinduction 1.20, MathComp algebra 2.3.0 and
analysis/reals-stdlib 1.13.0, matching the captured local contracts. In
particular, HB-generated names are part of elaborated types. These CI pins
do not tighten the library's package compatibility ranges or claim that newer
versions fail to compile; they keep the exact snapshot comparison reproducible.

Premises remain distinguished: representation parameters, semantic capability
classes, local program/handler contracts, theorem-specific mathematical
conditions, and global logical axioms. Fewer visible parameters is not a reason
to hide an assumption. Exact type checks prevent silently adding a transport
existence premise. Source checks reject new/changed classes, Axiom/Parameter
and incomplete proofs. A separate fixed logical-axiom whitelist protects
soundness even if a per-endpoint snapshot is accidentally updated.

The targeted kernel command checks 16 selected module bodies together with
`-norec`, in the AllImports universe context. Compiled dependencies are loaded
but not recursively rechecked. It is neither a whole-library proof audit nor
evidence of remote CI success. The separate final Gate D remains open.

Migration scripts, before/after snapshots and phase narratives are archived
in git, including accepted baselines `ec96b90`, `2258907`, `20e6ff2`,
`2af47aa`, `05a2431`, `3120df0`, `2dbba82` and Cleanup B baseline `5c1a0df`.
They are not repeatedly replayed as permanent runtime dependencies of audits.
