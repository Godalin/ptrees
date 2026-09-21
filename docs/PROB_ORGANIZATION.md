# Prob organization follow-up (before Gate D)

Source baseline: **`05a2431`**, after Gate C. This follow-up changes file
ownership and import/qualification paths, not definitions, theorem statements,
proofs, local contracts, class fields, or Stage 1–4 semantics. No adequacy
result or new probability capability is introduced. Pause for acceptance
before Gate D; do not proceed directly to StateInterp.

## Directory contract

The four existing top-level probability components remain:

```text
Prob/
  Interface/                 abstract operations and capabilities
  FreeOmega/                 canonical completion, generic in native MN
  Backend/
    Common/                  carrier-independent finite/arithmetic utilities
    Enum/                    raw finite weighted representation and adapters
      FreeOmega/             realization over raw Enum
    SubEnum/                 intrinsically bounded Enum carrier
      FreeOmega/             realization over SubEnum
    MathComp/                real-measure/kernel implementation
  Legacy/                    retained non-canonical weighted interfaces
```

`Prob/FreeOmega/Measure` is **not** a concrete backend. In contrast,
`Prob/Backend/SubEnum/FreeOmega/Total` fixes the native carrier. The ownership
audit enforces this distinction, rejects the old flat Backend layout, and
checks that Common cannot import a concrete carrier. MathComp and the
Enum/SubEnum implementation family cannot import one another.

Enum and SubEnum are not independent implementations: SubEnum validates the
raw Enum representation. Existing joint realization, finite presentation,
and disintegration modules therefore contain both raw-Enum construction
lemmas and SubEnum consequences. They remain under Enum, close to their
implementation. Enum's extended upper-observation theorem also reuses
SubEnum's bounded observation theory. These real dependencies are retained;
the directory grouping does **not** claim a one-way Enum/SubEnum dependency
or that every constant in an Enum module has only Enum arguments. Splitting
those additional proof chains is outside this conservative follow-up.

Legacy remains isolated by the generic/canonical ownership boundaries. It
is not beautified, deleted, or re-exported into the ordinary public API.
FiniteInternal's disposition is unchanged and awaits the adequacy audit.

## Interface extraction

`TwoLevelMeasure.v` is removed, with no compatibility wrapper. Its unchanged
declarations are distributed as follows:

| Module | Responsibility |
| --- | --- |
| `Measure` | `SemanticMeasure`, `CoreLaws`, `BindLaws`, equality instance |
| `Subprobability` | validity predicate, closure laws, intrinsic carrier law |
| `AE` | AELift, countable intersection, Kleisli, Dirac and exact-bind AE |
| `Coupling` | same-mass observation, coupling AE transport/restriction |
| `Omega` | order, limits, totality, AE limits, cofinality, diagonal/Fubini laws |
| `Mixed` | native/behavior bridge, ordinary/unit/node-bind/exchange/omega laws |

Existing `SemanticCoupling` remains the separate joint-realization capability;
`FrontierLift` remains an auxiliary interface, and `MeasureIteration` is
renamed `Iteration`. Class names and fields have not been renamed or split.
In particular CoreLaws still includes coupling composition. This is source
organization, not another redesign of the capability hierarchy.

## FreeOmega extraction

The 1,904-line `FreeOmegaMeasure.v` is removed and replaced by seven files:

| Module | Original declarations / purpose |
| --- | --- |
| `Definition` | `FreeOmega`, anchored carrier, bind, structural AE/lift |
| `Approximation` | `free_omega_approx`, cofinal chains, approximation bind |
| `Observation` | `free_omega_observes`, `free_omega_denotes`, denotation contracts and uniqueness |
| `StructuralMeasure` | auxiliary structural instances and their laws |
| `SupportLift` | high-universe support transport and algebra |
| `Quotient` | `free_omega_qlift` and support soundness |
| `Measure` | canonical observable semantic/mixed/omega instances and laws |

The two existing law Sections remain whole, with the same Context binders,
universe options, instance attributes and proof bodies. StructuralMeasure is
explicitly auxiliary; Measure implements the observable canonical quotient.
The structural totality definition already uses observations, so
StructuralMeasure legitimately imports Observation. Approximation's basic
relation is earlier in the DAG; its laws that use the structural measure
infrastructure remain in StructuralMeasure rather than creating a cycle.

Other generic files lose the redundant filename prefix: `Coupling`,
`JointExtension`, `Native`, `NativeCoupling`, `Recovery`, `Support`.
No old-name umbrella and no new bulk-export facade is introduced. Existing
clients explicitly import the split modules instead of the old monolith;
the newly extracted files list their own capability dependencies.

## Conservation evidence

The explicit [manifest](prob-organization.json) records 53 one-to-one moves,
the exact source-line partition of both split files, and declaration-owner
relocations. There are **220 modules** after extraction, up from 209.

`audit_prob_organization.py` reconstructs the expected tree directly from
`git archive 05a2431`. It checks every original line belongs to exactly one
payload or the shared preamble, then compares all resulting files exactly.
It permits only named import/namespace relocation, new extraction role
comments/import preambles, and the sorted AllImports list. It does **not**
strip comments, whitespace, theorem statements or proof bodies. Changed
Contexts, extra/deleted declarations and admitted proofs fail this audit.

The compiled checks are independent of that source comparison:

- The frozen Gate A 25-entry and Gate C 306-entry snapshots remain unchanged.
  Live checks compare full elaborated types and logical assumptions modulo
  the explicit declaration/module relocation map and printer line wrapping.
  They do not merely compare a set of class names.
- [PROB_CAPABILITY_BEFORE.json](PROB_CAPABILITY_BEFORE.json) additionally
  records 250 constants from the two pre-split modules, including datatype
  constructors, induction schemes, class projections and instances. The
  corresponding live constants must have the same elaborated type and
  `Print Assumptions` result. The baseline comes from `05a2431` compiled with
  the project's Coq/opam toolchain; the two self-contained old modules can
  also be compiled under their original logical paths in an isolated tree.
- Historical Gate B and Gate C conservation tools still audit their accepted
  revisions. Their rules are not loosened to accept this new migration.
- Audit-tool tests reject a changed proof, Context, comment, whitespace,
  dropped type premise, new axiom, lost module, or wrong backend owner.

No mathematical minimality, quotient adequacy, constructivity, or full
whole-library kernel-check claim follows from these checks.

## Validation

Run in the project's opam switch:

```sh
opam exec -- dune build
python3 tools/check_aggregate.py
python3 tools/audit_prob_organization.py
python3 tools/audit_prob_capabilities.py
python3 tools/audit_architecture.py --check
python3 tools/audit_capabilities.py --check --compare-baseline
python3 tools/audit_public_capabilities.py --check
python3 tools/audit_gate_c.py --revision 05a2431
python3 tools/audit_migration.py --revision 2af47aa
python3 -m unittest discover -s tools -p test_audit_tools.py
```

The follow-up also uses a single-process **27-module targeted** `coqchk`:
the six extracted interface files, all thirteen generic FreeOmega files,
the three native Measure modules, SubEnum/FreeOmega/Total, BackendCapabilities,
ArchitectureBoundaries, CapabilityBoundaries and AllImports. `-norec`
checks the explicitly named module bodies together and admits other dependency
bodies; this is not Gate D's all-library per-proof audit. AllImports still
loads every library module in a single universe context.

The exact targeted command is:

```sh
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Prob.Interface.Measure \
  -norec PTree.Prob.Interface.Subprobability \
  -norec PTree.Prob.Interface.AE \
  -norec PTree.Prob.Interface.Coupling \
  -norec PTree.Prob.Interface.Omega \
  -norec PTree.Prob.Interface.Mixed \
  -norec PTree.Prob.FreeOmega.Definition \
  -norec PTree.Prob.FreeOmega.Approximation \
  -norec PTree.Prob.FreeOmega.Observation \
  -norec PTree.Prob.FreeOmega.StructuralMeasure \
  -norec PTree.Prob.FreeOmega.SupportLift \
  -norec PTree.Prob.FreeOmega.Quotient \
  -norec PTree.Prob.FreeOmega.Measure \
  -norec PTree.Prob.FreeOmega.Coupling \
  -norec PTree.Prob.FreeOmega.JointExtension \
  -norec PTree.Prob.FreeOmega.Native \
  -norec PTree.Prob.FreeOmega.NativeCoupling \
  -norec PTree.Prob.FreeOmega.Recovery \
  -norec PTree.Prob.FreeOmega.Support \
  -norec PTree.Prob.Backend.Enum.Measure \
  -norec PTree.Prob.Backend.SubEnum.Measure \
  -norec PTree.Prob.Backend.MathComp.Measure \
  -norec PTree.Prob.Backend.SubEnum.FreeOmega.Total \
  -norec PTree.Regression.Backend.BackendCapabilities \
  -norec PTree.Regression.Infrastructure.ArchitectureBoundaries \
  -norec PTree.Regression.Infrastructure.CapabilityBoundaries \
  -norec PTree.Regression.Infrastructure.AllImports
```

Local validation completed: full `dune build`, the 220-module aggregate and
ownership checks, exact source conservation, the 25/306 endpoint comparisons,
all 250 extracted-constant comparisons, historical Gate B/C conservation,
34 audit-tool tests, and the 27-module joint targeted kernel check (exit 0).
The layout/client report was regenerated. No new axiom or admitted proof was
introduced. No remote CI result, completed Gate D, or FreeOmega adequacy
claim is made. This follow-up is ready for review, not self-accepted.
