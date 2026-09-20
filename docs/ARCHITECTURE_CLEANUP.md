# Theory-freeze preparation: architecture and assumptions

Stage 1–4 are accepted at `4703035`, `268a223`, `8e09561`, and
`ec96b90`, respectively. Do not extend their mathematics during this cleanup.
An actual correctness bug or a changed semantic contract requires separate
review. No StateInterp or FreeOmega adequacy development starts here.

## Review gates

| Gate | Deliverable | Status |
| --- | --- | --- |
| A | unique ownership policy, complete module inventory, compiled capability baseline | implemented; awaiting review |
| B | migrate/split modules, strict facades, role comments, experimental disposition | pending |
| C | minimize capabilities, remove unused contexts/imports, audit every agreed public endpoint | pending |
| D | final dependency checks, facade regressions, full joint kernel audit and scope review | pending |

Pause at each gate. Gate A deliberately changes no `.v` file: it makes the
starting obligations checkable before namespace and proof changes are mixed.
The whole cleanup is **not** complete at Gate A.

## One ownership model

The conceptual model remains syntax -> stable hitting -> canonical equality
and quantitative observations. A code dependency arrow has a different
meaning: it points from a component to the components it **uses**.

| Owner | Responsibility | Permitted lower-level dependencies |
| --- | --- | --- |
| `Core` | tree syntax, observe, primitive bind/iter/interp/translate, syntax utilities | external foundational libraries; no local measure or behavioral module |
| `Prob/Interface` | operations, laws and measure-only relational interfaces | other probability infrastructure; no PTree syntax |
| `Prob/FreeOmega` | formal omega completion and measure-only proofs | generic probability interfaces; no concrete backend or PTree theory |
| `Prob/Backend` | concrete measure implementations and specialized FreeOmega realization proofs | probability infrastructure; no tree equality |
| `Prob/Legacy` | still-used weighted/old measure adapters | probability infrastructure; not the canonical probability contract |
| `Eq` | stable hitting, peutt, stronger structural proof relations, probability validity, algebra | Core, Prob; not comparison semantics or interpreter compositionality |
| `Eq/Internal` | execution certificates and schedule/kernel adequacy proof machinery | Core, Prob, lower-level Eq infrastructure; no new equality API |
| `Semantics` | independent observations, transitions, MDPs, comparison/coincidence | Core, Prob, Eq; not Interp |
| `Interp` | interpreter compositionality | Core, Prob, Eq; Atomic/MDP additionally use Semantics |
| `API` and top-level facades | curated user-facing assembly and tree/backend adapters | the needed lower layers, without indiscriminate Export |
| `CaseStudies` | applications demonstrating equational usability | maintained library/API; no Regression or Experimental |
| `Regression` | positive/negative contract tests and integration harnesses | any tested layer; may reuse case-study results |
| `Experimental` | explicitly unsupported active experiments | never imported by maintained theory or CaseStudies |

This is acyclic at the ownership level: Semantics and the basic interpreter
theory share Eq; MDP interpretation can use Semantics, **not vice versa**.
Strict assembly belongs above both, not inside Eq where exporting an
interpreter would restore a reverse edge.

`API/Enum` and `API/SubEnum` are tree-facing convenience adapters. They do
not belong in measure-only `Prob/Backend`: `Prob mu Ret` already mentions
PTree syntax. Conversely, `FreeOmegaTotalSubEnum` is measure-only and does
belong in the concrete probability realization layer.

### Generic, canonical model, concrete endpoint

Use three visibly distinct levels, without adding a new all-purpose class:

1. Expert generic theory: independent `MN`, `MF`, operations and law packages.
2. Canonical model: choose `MN`, set `MF := FreeOmega MN`, derive behavioral
   capabilities from the explicitly required native capabilities.
3. Concrete endpoints: SubEnum or MathComp implementations, with extra
   gluing/total-map/other obligations stated wherever not already proved.

The present guarded/atomic/MDP interpretation implementation is
**FreeOmega-qualified**, even when its effects are generic `E -> F`.
Do not call it arbitrary-`MF` interpretation. Accordingly the target homes
are `Interp/FreeOmega/{Base,Guarded,Atomic,MDP}` and
`Interp/Backend/SubEnum`. This refines the proposed flat Interp directory
without changing any theorem or generalizing the homogeneous atomic profile.

Ordinary clients should eventually use curated `PTree`/`Semantics` entry
points; backend implementers deliberately import `Prob/...`; advanced
equational users may explicitly import implementation modules. These are
target import contracts, **not currently available top-level facades**.

## What the actual inventory found

The [machine-generated inventory](ARCHITECTURE_AUDIT.md) covers all 200
modules using Coq's `.PTree.theory.d`. The integration harness imports all
199 others and is excluded from substantive client counts.

- `Core/PTreeDefinition` imports the old `Prob/Monad` because `stuckM`
  uses `MonadMeasure`/`score`. Removing that import alone is incorrect:
  relocate the weighted convenience program, preserving its clients.
- `Core/PTreeProbability` is a probability-validity predicate with closure
  theorems, not primitive syntax. Move it to `Eq/WellFormedness`.
- `Core/PTreeEnum` and `Core/PTreeSubEnum` are tree/backend adapters.
- `Prob/EnumCofinality` proves tree bind-scheduling results and imports Eq;
  move it to `Eq/Backend`, not another measure-only Prob folder.
- The five principal interpreter files have clear move targets, but that
  is **not all interpretation infrastructure**. `Eq/FreeOmega/Base` has
  translation sections; `Eq/FreeOmega/Bind` has interpreted hitting/schedule
  sections. Split those dependencies rather than retaining reverse imports.
- `Eq/FreeOmega/Base` imports `DiscreteMC`, `FrontierLiftEnum` and
  `TwoLevelMeasureEnum`, although its declarations use generic `MN`.
  Those concrete imports are candidates for a compile-tested removal;
  textual absence alone is not proof that notation or instances are unused.
- `Eq/FreeOmega.v` is an expert bulk export, not the curated facade. Moving
  Interp while leaving this export unchanged would preserve the architectural
  problem. Replace its assembly role at the API layer; no compatibility
  wrappers should conceal the old ownership.

### FiniteInternal: do not confuse a name with a discarded relation

`finite_internal` is an inductive execution certificate to a distribution
of residual trees, not `pfinite` and not another behavioral equivalence.
The complete client report distinguishes ordinary and regression clients.
Schedule and kernel adequacy modules remain proof infrastructure; group them
under `Eq/Internal` rather than presenting them alongside peutt as peers.

Do not delete this family wholesale, nor call every member indispensable
merely because AllImports imports it. For each regression-only component,
Gate B must decide whether it tests a maintained certificate contract or
is a superseded experiment. Zero clients is evidence to investigate, not
proof of dead code. No deletion has been authorized by this inventory alone.

### Experimental and regression boundaries

There is one Experimental file: `UniverseSeparatedPTree`. It has no
ordinary incoming client and consists of positive representation probes
and checked negative MathComp universe examples. The disposition is to
reclassify the useful checks under Regression/Infrastructure, not promote
its alternate `uptree` representation as maintained theory. Revise the
historical migration wording when moving it: today's canonical two-level
FreeOmega model is not awaiting that proposed representation change.

The fixed contract-test catalogue includes InterpExposure, GuardedInterp,
AtomicInterp, MDPInterp, MDPCoincidence, BackendCapabilities, FreeOmega
limit/escaping-mass tests, and SubEnum total-map endpoints. CaseStudies
remain application proofs; do not move a negative API test there because
it happens to define an example program.

## Five kinds of premise, audited separately

| Kind | Examples | Evidence |
| --- | --- | --- |
| A: structural parameters | E/F, R, MN/MF, trees, relations | elaborated type |
| B: operations | SemanticMeasure, SemanticOmega, MixedMeasure | elaborated type and concrete instantiation |
| C: backend laws | CoreLaws, CouplingAELaws, CountableAELaws | elaborated type; later minimization proof |
| D: local semantic contract | guarded_handler, atomic_handler, mdp_handler, total-map premise | full theorem type, not Print Assumptions |
| E: logical axioms | funext, choice, excluded middle, eq_rect_eq | Print Assumptions |

The [capability baseline](CAPABILITY_BASELINE.md) queries **25 selected**
compiled definitions/helpers/endpoints using `Check @...` with implicit
arguments displayed and `Print Assumptions` separately. It includes bind,
iter, guarded/atomic interpretation, MDP coincidence and MDP interpretation.
The raw types preserve carrier assignments and local premises; the summary
collapses repeated class names only for readability.

Observed differences that a source-Context census would get wrong:

| Endpoint | Operations on MN | Law parameters retained by Rocq |
| --- | --- | --- |
| guarded_handler | Measure, Omega | none |
| atomic_handler | Measure, Omega | none |
| mdp_handler | Measure, Omega | Core |
| guarded_handler_of_hitting | Measure, Omega | Core, CouplingAE, CountableAE |
| mdp_state_interp | Measure, Omega | Core, CouplingAE, CountableAE |
| peutt_interp_guarded | Measure, Omega | Core, AELift, CouplingAE, CountableAE |

In particular `mdp_state_interp` already drops unused `NAE`, while the
guarded congruence retains it. A smaller exported parameter list cannot
be claimed just from deleting the former's unused source Context entry.
Similarly `mdp_handler` has an inherited `eq_rect_eq` logical dependency,
even though it is a definition: definitions may refer to proof-bearing
infrastructure. Do not describe `Print Assumptions` as a theorem-only audit.

`Htotal_map` remains a genuine local premise of the generic atomic MDP
route; the SubEnum endpoint discharges it. A concrete endpoint with no
class parameters is **instantiated**, not model-independent.

Gate C must still inspect proof bodies for overstrong helpers, minimize
unused contexts/imports, and extend this selected list to all agreed public
endpoints. Do not label the current 25-endpoint snapshot exhaustive or
mathematically minimal. Preserve before/after full signatures; any change
to a local semantic contract needs explicit review.

## Validation and completion criteria

Gate A has no `.v` modifications, no new axioms, no module moves and no
new public API. Its executable checks are:

```sh
opam exec -- dune build
python3 tools/check_aggregate.py
python3 tools/audit_architecture.py --check
python3 tools/audit_capabilities.py --check
python3 -m unittest discover -s tools -p test_audit_tools.py
```

The existing Stage 4 targeted joint `coqchk` is also rerun in the
AllImports universe context. That checks the named modules and the harness;
it is **not** a full per-proof kernel audit of all 200 modules. The full
joint audit is a Gate D requirement and must report actual completion.

Gate A local validation completed successfully: all five commands above,
the unchanged historical layout report, and this targeted joint check:

```sh
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Regression.Infrastructure.AllImports \
  -norec PTree.Prob.FreeOmegaTotalSubEnum \
  -norec PTree.Semantics.MDPInterp \
  -norec PTree.Semantics.MDPInterpSubEnum \
  -norec PTree.Regression.Semantics.MDPInterp
```

All `.v` files are unchanged from `ec96b90`. The eight audit-tool tests
include negative cases for Coq errors with a zero process exit code,
missing output markers, unparseable logical assumptions, and unclassified
experiments. No remote CI outcome is asserted.

Final cleanup acceptance additionally requires: enforced target dependency
directions; no interpretation scattered back into Eq/Semantics; explicit
generic/FreeOmega/backend profiles; module role comments; reviewed
FiniteInternal and Experimental dispositions; facade positive/negative
tests; all public endpoint capability and logical audits; source Context
hygiene; updated THEORY_STATUS; and no silent semantic changes. Only then
start the separately reviewed FreeOmega adequacy audit, not StateInterp.
