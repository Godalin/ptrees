# Case-study algebraic presentation refactor

Baseline: `e969912`. Standard: [CASE_STUDY_STANDARD.md](CASE_STUDY_STANDARD.md),
approved with four clarifications. Local validation only; CI is not queried.

## Scope and stable contracts

This is a presentation/consumer refactor, not a new semantics or probability
model. Program definitions, externally consumed theorem statements, public
probability results and extraction roots remain stable. Internal helpers may
change with an explicit replacement; compiled snapshots are not silently reset.

The 20 source files below are the entire current Examples inventory. A retained
analysis file is an intentional outcome, not an unfinished attempt to turn
convergence or invariant arguments into rewrite scripts. Headers now identify
each file's role, proof mode, reading entry and claim boundary.

## Changes and disposition

| File (relative to `theories/Examples`) | Role / main mode | Treatment |
| --- | --- | --- |
| `FactoryController.v` | Paper / algebraic | Isolate `fair_binary_round_step` before the main calculation. Its statement uses native `sem_bind`/`sem_ret`; only its proof consumes the concrete finite identity. Main chain rewrites directly inside the manufacturing step and through the full handler stack. |
| `ITreeSampling.v` | Supporting / algebraic | Replace manual bind congruence with elaboration rewrites. Keep the unbounded iter endpoint, without claiming AST. |
| `EffectInteractions.v` | Supporting / algebraic | Rewrite sampling elaboration and State equations; retain the separate lawful-target StateT theorem and its uniformity premise. |
| `StateRewrite.v` | Paper / algebraic + execution | Lift the sampling-fusion equation by contextual rewriting, then rewrite under State. Preserve differing fuel/trace and missing-mass checks. |
| `StateCounter.v` | Shared execution demo | Retain exact structural equation and replay correctness. Concrete coin/quantile computations belong to execution validation, not a paper rewrite chain. |
| `RationalState.v` | Shared execution demo | Retain partial native distribution and all Lost/Timeout/EntropyExhausted distinctions. |
| `BernoulliFactory/BernoulliFactoryComposition.v` | Paper/shared algebra | Replace repeated structural/coupling and hand-applied bind/iter congruence by generic algebra. Keep the finite-round analysis as a clearly identified local endpoint. |
| `BernoulliFactory/BernoulliFactory.v` | Shared program/finite analysis | Retain concrete distribution definitions and the exact finite-round identity consumed by both composition and controller. |
| `BernoulliFactory/BernoulliFactoryProbability.v` | Shared validity analysis | Retain native validity proofs; normalization is not a termination assertion. |
| `BernoulliFactory/VonNeumannUnbounded.v` | Shared convergence analysis | Retain finite approximation and arbitrary normalized-bias convergence proofs. |
| `BernoulliFactory/RationalBernoulli.v` | Shared convergence analysis | Retain arbitrary rational target, boundary cases and exact finite distributions. |
| `BernoulliFactory/OperationalVonNeumann.v` | Shared hitting analysis | Retain support/hitting/limit bridge and raw/compiled behavioral endpoints. |
| `BernoulliFactory/OperationalRationalBernoulli.v` | Shared hitting analysis | Retain `peutt_binary_rational_coin_direct` and AST results. |
| `BernoulliFactory/OperationalBernoulliFactory.v` | Shared hitting analysis | Retain `peutt_factory_vn_fair` and `peutt_factory_standard_direct`; these are substantive analyses, not hidden composition proofs. |
| `BernoulliFactory/RealBernoulliOracle.v` | Shared analysis/program | Retain binary-oracle representation conditions and missing-mass convergence. |
| `BernoulliFactory/RealBernoulliMathComp.v` | Shared native MathComp analysis | Retain normally universe-checked measure/lub proof and its representation premise. No direct recursive frontier is introduced. |
| `InteractiveVonNeumann/InteractiveVonNeumannService.v` | Paper / relational-coinductive | Retain the explicit request/reply simulation and its support/quantitative certificates. Do not conceal the invariant behind a purported unconditional loop rewrite. |
| `MixedHeadProtocol.v` | Paper / relational-coinductive | Retain mixed return/visible-head invariant, finite coupling analysis and quantitative observation endpoint. |
| `RandomWalk.v` | Paper / analysis + structural control flow | Retain height-translation stopping invariant, successive-passages normalization and harmonic/limit analysis. No unproved probability-to-bisimulation converse. |
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
