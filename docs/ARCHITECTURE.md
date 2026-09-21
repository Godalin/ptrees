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
| `Prob/Backend/{Common,Enum,SubEnum,MathComp}` | Arithmetic, native models and their specialized endpoints | Common has no native-carrier dependency; MathComp is independent of Enum/SubEnum |
| `Prob/Domain` | Independent continuous expectations and standard measure correspondence | Domain and mathematical libraries only |
| `Eq` | Stable hitting, `pstruct`, `pstrong`, canonical `peutt` | No Semantics, Interp or API dependency |
| `Semantics` | Raw/head transitions, comparison bisimulation and MDP fragment | No Interp or API dependency |
| `Interp` | Structural and behavioral interpreter theory | May consume Eq and Semantics |
| `API` | Curated endpoints and convenience programs | No bulk implementation export |
| `Examples` | Applications and program proofs | No Regression dependency |
| `Regression` | Positive, negative, integration and capability tests | Not formal library dependencies |

In Eq, Semantics and Interp, the `FreeOmega/` namespace fixes only
`MF := FreeOmega MN`; `Backend/` additionally fixes a native model. These
are different specializations. Generic layers cannot import either kind
of specialization, and canonical-model layers cannot import concrete ones.
Enum and SubEnum can reuse each other's realization facts: SubEnum is a
validated Enum carrier, not an unrelated implementation.

`Prob/Legacy` remains noncanonical weighted infrastructure. It is not an
alternative to the subprobability-validity contract. Its existing clients
are retained; no deletion follows merely from its name.

## Program-facing versus expert imports

```coq
From PTree Require Import PTree.     (* curated canonical reasoning API *)
From PTree Require Import Semantics. (* curated comparison semantics *)
```

The facades deliberately expose selected notation/aliases, rather than
re-exporting approximation, scheduling, quotient implementation or concrete
backends. `Core` does not expose probability interfaces. The canonical
behavioral relation is `peutt`, with notation `≈ₚ` / `≈ₚ[RR]`; auxiliary
structural relations are not competing public behavioral semantics.

Expert clients import actual owners. In particular, `Eq/PEutt` no longer
forwards `Eq/StableHittingRelation`, and the three SubEnum FreeOmega
UpperExpectation/UpperCoupling/UpperContinuity modules no longer forward
`Prob/Backend/SubEnum/Expectation`. The latter owns finite expectation,
AE extensionality and finite/countable-sup interchange. Its dependency
closure, and that of native `SubEnum/Domain`, exclude FreeOmega.

## External validation is one-way

Only named validation adapters may connect the independent domain with
SubEnum/FreeOmega or PTree. In particular, Common/DomainTransport and
Common/CountableCoupling connect independent scalar transport to OmegaVal;
they are not ordinary mainline Common dependencies.

The transitive closures of PTree/API/peutt/Eq-FreeOmega/Interp/Examples
exclude all validation modules. The model validates reasoning infrastructure;
reasoning infrastructure does not assume its own validating model.
Interpretation remains FreeOmega-qualified, not a claim about arbitrary MF.

## Internal proof facilities and tests

FiniteInternal is auxiliary proof infrastructure for well-founded internal
compression and related adequacy arguments. It is not part of the canonical
PTree semantics or public equivalence theory. The peutt/Interp/facade closure
does not use `Eq/Internal`; the final SubEnum domain-soundness proof does not
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
for 306 public/helper endpoints (including the original 25 capability probes)
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
