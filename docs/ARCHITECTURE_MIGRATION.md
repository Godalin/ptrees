# Gate B: implemented ownership boundaries

Gate A is frozen at `2258907`; interpretation Stages 1–4 remain the accepted
theory through `ec96b90`. This is an architecture migration, not a new
interpretation theorem, capability-minimization pass, or FreeOmega adequacy
claim. Gate B is submitted for review; stop before Gate C.

## What moved, and what was split

The [machine-readable manifest](gate-b-moves.json) records **105 moves**.
The source inventory grows from 200 to 208 modules: five extracted modules,
two top-level facades, and one import-boundary regression. Original theory
declarations are retained; no old-namespace compatibility wrappers remain.

| Original mixed-responsibility module | Extracted responsibility / new home |
| --- | --- |
| `Core/PTreeDefinition` | weighted convenience programs `stuckE`/`stuckM` → `API/Weighted` |
| `Eq/PStruct` | structural interp/handler/translate preservation → `Interp/Structural` |
| `Eq/PTreeKernel` | generic interp head/diagonal/hitting infrastructure → `Interp/Kernel` |
| `Eq/FreeOmega/Base` | translation approximants and preservation → `Interp/FreeOmega/Translate` |
| `Eq/FreeOmega/Bind` | interpreter schedules and cofinality → `Interp/FreeOmega/Cofinality` |

The main interpreter modules now live in `Interp/FreeOmega/{Base,Guarded,
Atomic,MDP}`, with the concrete endpoint in `Interp/Backend/SubEnum`.
`MDPCoincidenceFreeOmega` belongs in `Semantics/FreeOmega`, whereas
`MDPEmbeddingSubEnum` belongs in `Semantics/Backend`. Fixing the observable
model to `FreeOmega MN` is not fixing the native carrier to SubEnum.

Inspecting declarations rather than filenames identified further concrete
dependencies: `Coupling` and `IndexedCoupling` use Enum; `RelLift` uses the
legacy discrete interface; `FreeOmegaDisintegration` uses SubEnum. These
live in `Prob/Backend`, `Prob/Legacy`, and `Prob/Backend/FreeOmega`,
respectively. Tree-specific `EnumCofinality` lives in `Eq/Backend`;
SubEnum-specific `KernelDisintegration` lives in `Eq/Internal/Backend`.

Primitive `observe_interp`/constructor unfolding equations intentionally
remain in `Eq/Shallow`: they describe observation of Core combinators,
not interpreter preservation or comparison semantics. All compositionality
and interpreted-hitting infrastructure has moved to Interp.

## Enforced dependency direction

`audit_architecture.py` reads the actual coqdep graph and rejects forbidden
edges. It is no longer a list of proposed destinations:

- Core imports only Core among local modules; the old weighted-measure
  dependency has gone with the convenience programs.
- Prob interfaces and the canonical FreeOmega construction import no
  concrete backend, PTree syntax, or tree theory.
- Generic Eq/Semantics/Interp do not import FreeOmega specializations;
  generic and canonical-model layers do not import concrete endpoints.
- Eq imports neither Semantics, Interp nor API. Semantics imports no Interp
  or API. Interp may use Semantics for atomic and MDP preservation.
- API sits above these components. Maintained library components do not
  import tests or case studies; case studies do not import regressions.

This checks all **208 modules / 2038 direct local Require edges**. The
AllImports integration harness covers the other 207 modules but is excluded
from substantive client counts. Negative tool tests exercise forbidden
edges, including generic-to-canonical and canonical-to-concrete back-edges.

## Public surface

```coq
From PTree Require Import PTree.
From PTree Require Import Semantics.
From PTree.API Require Import SubEnum. (* optional concrete adapter *)
```

`PTree` exports the curated `API/Generic` and `API/FreeOmega` vocabularies.
`Semantics` exposes selected transition/MDP definitions and endpoints.
The old `Eq/FreeOmega.v` bulk assembly is removed: existing expert clients
now explicitly import the implementation modules they used. The canonical
facade does not load the concrete SubEnum backend. `API/SubEnum` is an
explicit concrete opt-in, including its atomic MDP endpoint.

The facade is a short-name/API boundary, not a claim that Rocq can hide
loaded constants from fully qualified lookup. Implementation modules are
loaded through `Require Import`, not indiscriminately re-exported. Expert
imports remain available. `ArchitectureBoundaries.v` separately checks
loading boundaries (qualified `Fail Check`) and public short-name exposure.
Independent Module scopes prevent an earlier Core import from accidentally
making a later facade's positive syntax checks pass.
Positive endpoint checks use `Check @...`, avoiding implicit instance search
on deliberately uninstantiated polymorphic API constants.

## FiniteInternal and Experimental dispositions

All finite-internal/kernel modules move under `Eq/Internal`; none defines
an additional behavioral equality. The [current inventory](ARCHITECTURE_AUDIT.md)
lists each module's ordinary and regression clients, excluding AllImports.
Retention is based on the following distinct proof contracts, not on merely
having a filename or being imported by the aggregate.

| Module(s), relative to `Eq/Internal` | Retained responsibility |
| --- | --- |
| `FiniteInternal` | well-founded internal execution-cut certificate |
| `FiniteInternalHitting` | certificate-to-hitting and peutt bridge |
| `FiniteInternalJoint` | correlated marginal completion witnesses |
| `FiniteInternalPlan` | informative internal execution plans |
| `FreeOmega/FiniteInternal` | certificate coverage of primitive approximants |
| `FreeOmega/FiniteInternalAcceleration` | repeated cuts and guard observation adequacy |
| `FreeOmega/FiniteInternalCostedCoinduction` | supplied correlated rounds imply peutt |
| `FreeOmega/FiniteInternalCostedProjection` | marginal costs and projected path certificates |
| `FreeOmega/FiniteInternalJoint` | paired native guard transitions |
| `FreeOmega/FiniteInternalJointAcceleration` | increasing joint-grid adequacy |
| `FreeOmega/FiniteInternalJointCoinduction` | explicit structural realization sufficient rule |
| `FreeOmega/FiniteInternalJointCoverage` | structural graph coverage premises |
| `FreeOmega/FiniteInternalJointHitting` | completion of a supplied correlated macro round |
| `FreeOmega/FiniteInternalJointReference` | two presentations of a common correlated process |
| `FreeOmega/FiniteInternalJointRows` | assembly from per-pair joint rows |
| `FreeOmega/FiniteInternalJointTruncation` | native joint truncations |
| `FreeOmega/FiniteInternalNative` | normalization to native path carriers |
| `FreeOmega/FiniteInternalNativeJoint` | joint construction under explicit native realization |
| `FreeOmega/FiniteInternalPlanHitting` | path-budget and hitting decomposition |
| `FreeOmega/FiniteInternalProjectedPolicy` | unary projected-policy adequacy premises |
| `FreeOmega/FiniteInternalRound` | native guard/round path encoding |
| `FreeOmega/FiniteInternalRoundCoupling` | coupling of guard/path carriers |
| `FreeOmega/CostedKernel` | nonuniform-cost observation grids |
| `FreeOmega/KernelCompletion` | completion from upper bounds, not a least-solution iff |
| `FreeOmega/KernelCongruence` | invariance under kernel representation changes |
| `FreeOmega/KernelContinuity` | increasing kernel-grid continuity |
| `FreeOmega/KernelProjection` | projection commutation with explicit premises |
| `Backend/KernelDisintegration` | concrete conditional-resampling preservation |

Regression-only clients still test these explicit contracts; they do not
establish unrestricted native realization or FreeOmega adequacy. Stale
comments referring to the removed residual GFP were corrected without
changing definitions or proofs. A separate adequacy audit remains pending.

`Experimental/UniverseSeparatedPTree` moves to `Regression/Infrastructure`.
Its positive and checked-negative representation probes remain intact;
the alternate `uptree` is not promoted into maintained theory. Historical
comments no longer suggest the canonical representation awaits that
experiment. No Experimental source remains; a new unclassified experiment
still makes the architecture audit fail.

## Conservation and validation

`audit_migration.py` compares with the frozen Git source at `2258907`:
197 original modules and five extracted Section bodies match after
normalizing comments, imports, whitespace and manifest namespace changes.
Three explicit assembly exceptions are the rewritten FreeOmega facade,
the generic facade's added syntax aliases, and AllImports. The SubEnum
adapter's added endpoint alias is stripped explicitly. No theorem or proof
body is silently excluded by a broad filename pattern.

The selected 25 compiled endpoint types and logical assumptions also match
Gate A after namespace normalization (`audit_capabilities.py
--compare-baseline`). The frozen reports remain byte-for-byte unchanged
as `ARCHITECTURE_BASELINE.md` and `CAPABILITY_BASELINE.md`; current reports
are separate. This is not exhaustive public-endpoint minimization.

Reproducible local checks:

```sh
opam exec -- dune build
python3 tools/check_aggregate.py
python3 tools/audit_architecture.py --check
python3 tools/audit_migration.py
python3 tools/audit_capabilities.py --check --compare-baseline
python3 -m unittest discover -s tools -p test_audit_tools.py
python3 tools/audit_layout.py
```

The historical layout auditor still verifies its frozen `92e0841 ->
6194bdf` proof-text comparison; its current client analysis now uses Gate B
paths. It does not mislabel Gate B as that earlier namespace-only change.

Local full build, AllImports and all 16 audit-tool tests have passed.
The targeted joint kernel check completed successfully (exit 0). It includes
the integration harness, public facades, extracted
interpreter modules, Stage 1–4 implementation/regression endpoints and the
new boundary regression. Gate D's full 208-module per-proof kernel audit is
distinct and remains pending. No remote CI result is asserted.

After the final import-scope adjustment, the final versions of AllImports
and ArchitectureBoundaries were jointly rechecked successfully with:

```sh
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Regression.Infrastructure.AllImports \
  -norec PTree.Regression.Infrastructure.ArchitectureBoundaries
```

Exact targeted command (one process, 24 named modules; dependencies are
loaded for joint universe consistency, not all recursively rechecked):

```sh
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Regression.Infrastructure.AllImports \
  -norec PTree.API.Generic -norec PTree.API.FreeOmega \
  -norec PTree.API.Weighted -norec PTree.API.SubEnum \
  -norec PTree.PTree -norec PTree.Semantics \
  -norec PTree.Interp.Kernel -norec PTree.Interp.Structural \
  -norec PTree.Interp.FreeOmega.Translate \
  -norec PTree.Interp.FreeOmega.Cofinality \
  -norec PTree.Interp.FreeOmega.Base \
  -norec PTree.Interp.FreeOmega.Guarded \
  -norec PTree.Interp.FreeOmega.Atomic \
  -norec PTree.Interp.FreeOmega.MDP \
  -norec PTree.Interp.Backend.SubEnum \
  -norec PTree.Semantics.FreeOmega.MDPCoincidenceFreeOmega \
  -norec PTree.Prob.Backend.FreeOmega.FreeOmegaTotalSubEnum \
  -norec PTree.Regression.Semantics.InterpExposure \
  -norec PTree.Regression.Semantics.GuardedInterp \
  -norec PTree.Regression.Semantics.AtomicInterp \
  -norec PTree.Regression.Semantics.MDPInterp \
  -norec PTree.Regression.Infrastructure.ArchitectureBoundaries \
  -norec PTree.Regression.Infrastructure.UniverseSeparatedPTree
```

The future whole-library check is `python3 tools/check_aggregate.py --kernel`;
this Gate B targeted run is not reported as that Gate D result.
