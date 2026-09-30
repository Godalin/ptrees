# Case-study algebraic presentation refactor

Baseline: `e969912`. Standard: [CASE_STUDY_STANDARD.md](CASE_STUDY_STANDARD.md),
approved, retaining the file-role, concrete-analysis and stable-endpoint
clarifications without a proof-method classification. Local validation only;
CI is not queried.

## Adaptive full-program calculation (baseline `62338b6`)

The [Adaptive case](ADAPTIVE_FACTORY_CONTROLLER.md) now follows the same
reading structure as FactoryController: setup, actual programs, analysis and
component equations, full-program calculation, then reusable consequences.
Everything stays in its existing file and `Adaptive` namespace.

- `controller_program_rewrite` opens the complete service round inside the
  relational iteration proof. Handler/State/bind/Vis equations form the
  calculation; it no longer calls a preproved service-iteration relation.
- `adaptive_factory_direct` shows the component calculation itself: the
  existing binary-factory equation, State/interpreter iteration, per-round
  algebra, and the adaptive VN fairness certificate. It no longer delegates
  its proof to a ladder of factory-step wrappers.
- Five deterministic private-event equations become one `lower_internal`.
  One-use finite recurrences, normalized-step and elementary frontier facts
  are proved at their use sites. The actual convergence and correlation
  arguments remain explicit; they are not disguised as rewriting.
- `service_refinement` and `controller_refinement` retain their interfaces
  as consequences, not prerequisites of the final calculation. Program
  definitions, quantitative results and recorded case endpoint types are
  preserved; no state reset or independence premise is introduced.
- A real generic rewriting gap is filled at `Eq/PEutt`: heterogeneous
  composition and equality-based rewriting of both endpoints of `peutt RR`.
  The old interpreter-local composition proof delegates to that owner.
  A minimal-context bool/nat client checks actual rewriting; no new backend
  class, case-local Proper instance or axiom is introduced.

The older checkpoint validation records below are historical, not current
module/test counts. Current validation for this follow-up is recorded in the
Adaptive case document.

## User-gallery follow-up (baseline `833d65b`)

The [learning guide](CASE_STUDIES.md) is a navigation layer, not another API
facade or a fixed paper selection. This follow-up leaves the foundational
theory and all existing program definitions unchanged:

- `IterationBasics.v` is a single-file SubEnumQ tutorial. Its main frontier
  proof applies the existing complete-step theorem; its classical comparison
  reuses ReturnIteration. Finite expectation rewriting and the existing
  rational geometric bound establish returned mass 1 or 1/2; unconditional
  retry has the exact zero frontier. The numerical analysis is not disguised
  as a program rewrite, nor does the file import external validation.
- `AbsorbingFrontier.v` retains its full existing program calculation and
  adds an exact actual-round certificate consumed directly by generic
  `iteration_summary_hitting`. A separate whole-head lifting theorem joins
  that witness to the fair mixed-head reference. Actual Vis continuations
  keep their bind syntax; behavioral equality is not used as tree equality.
- Adaptive's stale proof diagram no longer mentions a case-specific cofinal
  schedule. Its existing native observation convenience remains unchanged;
  documentation distinguishes conceptual specialization from proof reuse.
- Seven existing case files, including Adaptive, receive only reading comments. No invariant,
  convergence proof, extraction root or endpoint strength is changed.

The gallery points to behavioral/frontier/quantitative/execution endpoints
where they exist; it does not require each case to manufacture all four.

Local verification for this follow-up:

- Full `opam exec -- dune build -j 2`, including AllImports and extraction.
- 141 tool tests; architecture, API surface and source-soundness checks.
- 465 main contracts and 41 factory contracts unchanged. All 120 previous
  safe generic-algebra contracts were compared before appending 11 new case
  endpoints; the resulting 131-entry suite was then rechecked.
- New recorded semantic endpoints inherit only existing functional
  extensionality and/or `eq_rect_eq`; the continuation-shape check is closed
  under the global context. No axiom whitelist or exception is extended.
- All 12 previous AbsorbingFrontier proof declarations are preserved; seven
  other case files have unchanged code/proof tokens after removing comments.
- Joint `coqchk -norec` passes for IterationBasics and AbsorbingFrontier.
  Dependencies are trusted: this is not a recursive whole-library audit.
- The inventory is 448 modules, with the same two isolated Gate M files.
  Neither Gate M nor external-validation permissions change. CI is not checked.

## Scope and stable contracts

This is a presentation/consumer refactor, not a new semantics or probability
model. Program definitions, externally consumed theorem statements, public
probability results and extraction roots remain stable. Internal helpers may
change with an explicit replacement; compiled snapshots are not silently reset.

The 20 source files below are the Examples inventory at the refactor checkpoint.
The subsequently added [adaptive controller](ADAPTIVE_FACTORY_CONTROLLER.md)
is a separate case with completed behavioral refinement, not part of that
presentation-only refactor. A retained
analysis file is an intentional outcome, not an unfinished attempt to turn
convergence or invariant arguments into rewrite scripts. Headers now identify
each file's role, reading entry and claim boundary. Algebraic transformations
should use program equations; genuine analysis, bisimulation and invariant
arguments need not be disguised as rewrites.

## Changes and disposition

| File (relative to `theories/Examples`) | File role | Treatment |
| --- | --- | --- |
| `FactoryController.v` | Paper case study | Isolate `fair_binary_round_step` before the main calculation. Its statement uses native `sem_bind`/`sem_ret`; only its proof consumes the concrete finite identity. Main chain rewrites directly inside the manufacturing step and through the full handler stack. |
| `ITreeSampling.v` | Supporting example | Replace manual bind congruence with elaboration rewrites. Keep the unbounded iter endpoint, without claiming AST. |
| `EffectInteractions.v` | Supporting example | Rewrite sampling elaboration and State equations; retain the separate lawful-target StateT theorem and its uniformity premise. |
| `StateRewrite.v` | Paper case study | Lift the sampling-fusion equation by contextual rewriting, then rewrite under State. Preserve differing fuel/trace and missing-mass checks. |
| `StateCounter.v` | Shared execution demo | Retain exact structural equation and replay correctness. Concrete coin/quantile computations belong to execution validation, not a paper rewrite chain. |
| `RationalState.v` | Shared execution demo | Retain partial native distribution and all Lost/Timeout/EntropyExhausted distinctions. |
| `BernoulliFactory/BernoulliFactoryComposition.v` | Paper case study / shared support | Replace repeated structural/coupling and hand-applied bind/iter congruence by generic algebra. Keep the finite-round analysis as a clearly identified local endpoint. |
| `BernoulliFactory/BernoulliFactory.v` | Shared program/finite analysis | Retain concrete distribution definitions and the exact finite-round identity consumed by both composition and controller. |
| `BernoulliFactory/BernoulliFactoryProbability.v` | Shared validity analysis | Retain native validity proofs; normalization is not a termination assertion. |
| `BernoulliFactory/VonNeumannUnbounded.v` | Shared convergence analysis | Retain finite approximation and arbitrary normalized-bias convergence proofs. |
| `BernoulliFactory/RationalBernoulli.v` | Shared convergence analysis | Retain arbitrary rational target, boundary cases and exact finite distributions. |
| `BernoulliFactory/OperationalVonNeumann.v` | Shared hitting analysis | Retain support/hitting/limit bridge and raw/compiled behavioral endpoints. |
| `BernoulliFactory/OperationalRationalBernoulli.v` | Shared hitting analysis | Retain `peutt_binary_rational_coin_direct` and AST results. |
| `BernoulliFactory/OperationalBernoulliFactory.v` | Shared hitting analysis | Retain `peutt_factory_vn_fair` and `peutt_factory_standard_direct`; these are substantive analyses, not hidden composition proofs. |
| `BernoulliFactory/RealBernoulliOracle.v` | Shared analysis/program | Retain binary-oracle representation conditions and missing-mass convergence. |
| `BernoulliFactory/RealBernoulliMathComp.v` | Shared native MathComp analysis | Retain normally universe-checked measure/lub proof and its representation premise. No direct recursive frontier is introduced. |
| `InteractiveVonNeumann/InteractiveVonNeumannService.v` | Paper case study | Root/reply invariant with up-to-bind for the sampler context; retain explicit hitting and quantitative certificates. See `UP_TO.md`. |
| `MixedHeadProtocol.v` | Paper case study | Asymmetric programs: three/four Boolean draws versus one native draw. Finite hitting supplies the sampler relation; up-to-bind carries the same 3-to-2 joint into heterogeneous Ret and recursive Vis obligations. Generic bind recovers public Boolean equivalence; quantitative observations are retained. See `UP_TO.md`. |
| `RandomWalk.v` | Paper case study | Retain height-translation stopping invariant, successive-passages normalization and harmonic/limit analysis. No unproved probability-to-bisimulation converse. |
| `MathCompPrograms.v` | Supporting syntax | Retain safe retry/nested-retry definitions; actual direct-frontier clients stay in existing Gate M regressions. |

## File organization decisions

- The controller, mixed protocol and random walk already each have one main
  file. The interactive service also has one source file despite its directory.
- `StateRewrite.v` is the one paper-facing State case. `StateCounter` and
  `RationalState` remain separate because they are independently extracted
  demos and shared program/distribution inputs. Merging would mix execution
  roots and duplicate or obscure dependencies, not improve the main calculation.
- `BernoulliFactoryComposition.v` is the single composition entry. The shared
  VN/rational/hitting analyses also serve the controller, service and extraction;
  they are not copied or concatenated into each paper case.
- No files or tests are deleted; no wrappers are introduced to simulate a
  cleaner interface. Concrete native sampling remains explicit at definitions.

## Generic rewriting gap

`Vis` and `Prob` are syntax notations for `go (VisF ...)` and `go (ProbF ...)`.
The existing whole-node Proper theorems do not by themselves always solve the
decomposed morphism goals generated by `setoid_rewrite`. Generic one-layer
`peutt_visF_Proper` / `peutt_probF_Proper` in `Eq/Algebra` reuse `peutt_vis` /
`peutt_prob_Proper` and the existing `going`/`going_go` relation. No new
semantic relation, axiom, capability or backend-specific proof is introduced.

The opt-in completion module fixes the frontier for `ProbF` with one application
of the generic instance. The finite-round analysis in the composition example
retains two explicit `MF` arguments: leaving them unconstrained causes slow
search in that import context. This is a local disambiguation, not a new hint.
Pointwise iteration rewriting uses a `pointwise_relation` type ascription when
the step is passed unapplied; no function extensionality proof is introduced.

## Assumption comparison

All nine existing composition declarations were compared with the `e969912`
source re-elaborated in a fresh namespace against the current library. Each new
proof inhabits the old type and has no additional logical axioms. This is a
targeted comparison, not an independent rebuild of the entire old repository.
The stored `factory_with_sampler_Proper` contract retains its exact compiled
type and loses `relational_choice` and `dependent_unique_choice`; its dedicated
exceptions are removed. All other pre-existing generic-algebra entries remain
exact. The factory's 22 stored type/assumption contracts remain exact.

The new `ProbF` wrapper inherits `relational_choice` and
`dependent_unique_choice` from the existing generic `peutt_prob_Proper`.
These are recorded for its four new wrapper/client contracts using the existing
per-endpoint exception mechanism; the global whitelist is unchanged. The new
visible wrapper is closed under the global context. No wrapper postulates a
new law, and no pre-existing endpoint gains an assumption.

## Validation record

Completed locally on 2026-09-26:

- Full `opam exec -- dune build`, including AllImports, the existing extraction
  targets and Gate M compilation. This is not a claim that Gate M is
  universe-checked; its two-file boundary is unchanged.
- All 141 Python tests; architecture/report agreement, source soundness and
  public-surface checks; contract registry metadata validation.
- All 465 mainline compiled type/assumption contracts unchanged.
- Exact targeted suites: generic algebra (63), factory controller (22),
  ITree bridge (61), effect algebra (58), State rewrite (13). Generic algebra's
  single reviewed assumption reduction and six additions are described above.
- Nine-module joint `coqchk -norec`: `Eq.Algebra`,
  `Interp.FreeOmega.Rewriting`, both algebra/rewrite regressions, and the five
  modified examples. This checks safe module bodies while trusting compiled
  dependencies; it is not a whole-library recursive kernel audit.
- For the five proof-changing Examples, existing declaration headers and
  program definition bodies are source-identical after comment/whitespace
  removal. The other fifteen files differ only in comments/whitespace.
- Extracted controller implementation and specification both completed the
  scripted run with seed 2026 (32 and 4 native draws respectively). These are
  execution smoke checks, not a PRNG correctness or statistical equality proof.

No program, extraction root, probability model, routing or Gate M policy was
changed. No new audit script or historical-replay mechanism was added.
Remote CI was neither queried nor claimed as passing.

### Presentation-policy correction

After `166c92c`, the mandatory proof-method field and its classification table
were removed from the standard, this inventory and all 20 Examples headers.
File roles, concrete-distribution analysis boundaries and stable-endpoint
contracts remain. Each source change is exactly the deletion of one comment
line; definitions, proofs and imports are unchanged. The 11 factory tests and
source soundness check passed. No full build or kernel check was repeated for
this comment/documentation-only correction; the results above belong to the
preceding implementation refactor.
