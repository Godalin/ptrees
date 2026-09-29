# Regression organization and retention

The directory cleanup started from `119ed4e`. It removed development-history artifacts,
groups related current contracts and corrects source ownership; it does not
change probability interfaces, PTree semantics or the MathComp trust boundary.

## What belongs here

Compiled contracts pin a declaration's type and assumptions. They do **not**
test typeclass inference, `setoid_rewrite`, minimal imports, import order,
concrete observations or rejected ill-typed programs. Those remain Rocq tests.
Positive integration clients are legitimate regressions when they exercise
these properties; regression is not synonymous with negative example.

| Directory | Responsibility |
|---|---|
| `Backend` | Native representations, actual instance inference and backend clients; isolated MathComp Gate M client |
| `Probability` | Independent-model, transport, support, limit and quotient boundary contracts |
| `Semantics` | Equational/transition/handler clients and semantic counterexamples |
| `Execution` | Concrete runner, replay and finite-execution checks, including resource failure distinctions |
| `Infrastructure` | Aggregate, public surface, capability and checker boundaries |
| `ImportOrder` | Independently compiled canonical routing probes |
| `Internal` | Clients of auxiliary scheduling, compression, kernel and recovery proofs |
| `Fixtures` | Shared test data; not a public semantic layer |

`Examples` is for readable program proofs. The small public-equation client
formerly named `HandlerCalculus` now lives in `Examples/RealSamplingHandler.v`.
`HittingPrograms` remains a low-level integration test, not a paper case.
That directory pass introduced no production capability. The subsequent
theorem-promotion pass below adds derived laws, not new capability assumptions.

## Theorem promotion: silent behavior and transition laws

Starting from `1f3c03c`, review the mathematical responsibility of a proof,
not its filename or number of lines. A reusable semantic law belongs in its
production owner. A readable concrete program argument may belong in Examples.
Negative boundaries and positive integration/inference clients remain tests.
Having parameters alone does not turn a fixture theorem into public theory.

This is a targeted first promotion pass, **not an exhaustive semantic audit of
every lemma in all 105 regression modules**. No modules are removed or merged.

| Reviewed proof family | Disposition |
|---|---|
| `GuardedInterp.handler_spin_hitting_zero` | Instantiate generic `ptree_stable_hitting_spin_zero` |
| `CanonicalPartialDivergence` spin approximants/hitting | Remove duplicate approximant lemmas; use generic zero hitting; keep partial-mass and separation tests |
| `HeadTransition.divergent_response_has_empty_support` | Derive from generic zero hitting and existing quotient support transport; keep the actual transition witness |
| `StableHittingDomain` silent bottom/native loss/Ret/Vis | Model laws now live in `Eq/Backend/StableHittingDomainSubEnumQ`; tests only instantiate them |
| `MDPCoincidence.delay_transition_bisim`, `MDPInterp.hetero_delay_transition_bisim` | Instantiate `Semantics/TreeTransitionBisim.trans_bisim_tau_l`; its proof is independent transition coinduction |
| `ProbabilisticRelationHierarchy` divergence/Tau and stopping clients | Keep: negative hierarchy boundaries and eventful/unreached stopping applications |
| `UnrestrictedInterp.partial_mixed_handler` | Keep: positive integration of returning, divergent and visible handler behavior, not another divergence theorem |
| `Execution/FiniteDistribution` spin | Keep: fuel timeout versus semantic loss is a runner contract, not redundant zero-hitting analysis |
| `HittingPrograms`, `FreeOmegaUpperContracts` | Keep concrete integration/numerical counterexamples; do not promote fixture-specific distributions as generic laws |
| `Internal/FiniteInternalPlan` spin | Keep: stopped-path planning fixture, not the canonical hitting theorem |
| `OmegaValMeasure`, `FreeOmegaOrder`, `ImportOrder/*`, MathComp universe probes | Keep independent-model, order, elaboration and trust boundaries |

### Production endpoints and assumptions

`Eq/PTreeKernel` owns five new derived laws:

- `ptree_hitting_tau_closed_zero`: a Tau-closed invariant implies zero finite
  approximants. It needs frontier Core/Bind laws and operations, but **no native
  SemanticMeasure, native omega, countability, totality or FreeOmega**.
- `ptree_stable_hitting_of_zero_approximants`: transports the constant zero lub
  along semantic equality. Its compiled type does not need Bind laws.
- `ptree_stable_hitting_tau_closed_zero` and `ptree_stable_hitting_spin_zero`:
  complete zero frontier, using existing Omega laws (chain properness) and
  Cofinality laws (constant lub). No new `spin` syntax is necessary: the latter
  consumes `observe t = TauF t`, so existing cofixpoints work unchanged.
- `ptree_stable_hitting_prob_empty`: empty native AE support implies zero
  hitting for **arbitrary continuations**. It uses Mixed laws and
  `mixed_bind_zero`, not a native omega or normalization assumption.

The Cofinality capability here is the existing owner of `sem_lub_constant`;
this pass neither splits that class nor hides its actual requirement.

The external model owner adds `ptree_domain_hitting_of_denotes`, then zero,
Ret, Vis, Vis-mass, spin, empty-native and native-zero corollaries. Every one
follows through existing stable-hitting denotational adequacy. There is no
second induction over the mathematical approximants and no reverse import
from generic Eq into the external model. The model proof deliberately inherits
adequacy's audited classical/extensional dependencies; no axiom is introduced.

`trans_bisim_tau_l` / `trans_bisim_tau_r` are generic homogeneous transition
laws. The left law uses the candidate `a = b \/ a = Tau b`; the right law uses
symmetry. Neither imports nor calls `peutt`. The MDP regressions still start
from independent transition evidence, including distinct source/target effects.

Retained tests exercise actual specializations. An additional changing-state
silent counter tests Tau-closed invariants beyond the single self-loop equation.
The stable-head Vis law concerns the **next observation**, not termination of
an infinite interactive service. Native loss and infinite internal divergence
both have zero stable mass, but runner `Lost` and `Timeout` remain distinct.

The existing compiled-contract runner records the new production signatures
and assumptions; no new audit executable, historical replay, checker bypass,
semantic class, or global inference hint is added. All prior contract entries
are retained verbatim. CI remains out of scope.

Local validation of this promotion pass:

- Full `opam exec -- dune build -j 2` passed, including AllImports and
  extraction. The initial higher-concurrency build timed out at the existing
  `FactoryController` Qed; neither that proof nor its timeout/environment was
  modified. The failed attempt is not counted as a pass.
- All 143 Python tests, architecture, public-surface, source-soundness and
  contract-registration checks passed.
- Central compiled contracts: **465 unchanged + 15 new = 480**, all checked.
  The 52-entry generic MDP group also passed. An earlier MDP query during
  rebuilding encountered a missing `.vo`; the successful rerun supersedes it.
  Other compiled groups were not rerun in this pass.
- The seven new generic endpoints are closed under the global context; the
  eight external-model endpoints use only the existing logical-axiom whitelist.
- Joint `coqchk -norec` passed for the three production owners and six changed
  regression modules. Dependencies were trusted; this is neither an exhaustive
  recursive audit nor a Gate M kernel check.
- One-off source comparison confirmed that the three production files retain
  all pre-existing source exactly; only new sections/theorems were inserted.
- Regression source is reduced by 117 lines across six files. Five duplicate
  approximant lemmas and an unused coinduction candidate are removed; their
  old code remains available at `1f3c03c`. All 105 regression files remain.

## Changes and deliberate non-deletions

- Remove the historical `RationalRepresentationMigration` certificate. It had
  no substantive clients; the old `nnQ` representation is not a second backend.
- Consolidate positions/presentation/pruning/algebra/shared-carrier checks in
  `Backend/FiniteLists`, removing six obsolete `nnQ` conversion checks. Keep
  signed observables, duplicate and zero entries, positions and high universes.
- Consolidate frontier-iteration contracts, runner
  outcomes, rational replay, internal kernel clients and MDP encodings. Nested
  modules preserve local names and proof contexts. Imports stay outside module
  wrappers. Early negative dependency probes run before concrete test imports.
- Keep `GenericAlgebra`, `GenericConsumers` and `RelationalConsumers` separate.
  Their minimal-profile sections precede concrete backend loading; moving that
  loading ahead of the generic clients needlessly expands typeclass search.
  Only the redundant aliases are removed from these files.
- Remove fifteen bare endpoint aliases whose **production declarations remain
  contracted**, and one duplicate bind application covered by `PublicBehavior`.
  Real rewriting/inference clients stay; no mainline contract is retired.
- Move the six quotient-equality/approximation counterexamples formerly in
  `GenericBind` to `Probability/FreeOmegaOrder`. Equality must not be assumed
  to imply approximation order.
- Keep pure `OmegaVal` and `OmegaValMeasure` tests separate: their independent
  import boundaries differ. Keep the three routing import-order units separate.
- Keep `FreeOmegaEscapingMass` and `FreeOmegaLimitSafety`: observation escape,
  diagonal/cofinality misuse and countable matrix escape are different failures.
- Keep `FreeOmegaUpperContracts`: besides concrete observations it supplies the
  jointly loaded universe context for the MathComp positive/negative probes.
- Keep `FreeOmegaSamples`: five model/transport test clients share its samples.
  Do not duplicate those witnesses merely to remove a directory.
- Keep `MathCompOrder` separate from `MathCompOmega`: it tests missing omega
  capability under the smaller import. Keep MathComp's actual inference and
  program clients in Regression, not Examples; Gate M stays exactly two files.
- Keep `FiniteInternalPlan`: it tests nonuniform/stopped paths and is consumed
  by round, cost and recovery clients. Its name does not make it a roadmap.
- Keep heterogeneous MDP interpretation, non-Dirac successors and independent
  transition-side evidence; two encoding clients share a file, but these distinct
  fragment and interpreter contracts are not replaced by correspondence aliases.
- Keep execution contracts: `Lost`, `Timeout` and `EntropyExhausted` must remain
  distinct. A distribution theorem's signature cannot test an actual replay.

### Runner fixture universe correction

The expanded joint kernel check exposed a pre-existing fixture issue: passing
bare template-polymorphic `option` as the native higher-kinded argument could
check in isolation but fail after loading the full safe library. Recompiling
the original `119ed4e` execution test in a fresh namespace reproduced the
failure at `test_run`; removing only that alias merely moved the failure to
`closed_choice`. Disabling universe minimization did not solve it.

The merged runner fixture instead uses a local abbreviation for
`fun X : Type => option X`. This is the same data representation, eta-expanded
at the functor boundary, with no new sampler law or semantic assumption.
Its test programs and proof scripts are otherwise retained. Three contracted
test types now explicitly print that lambda; all production types and the
fourth generic outcome contract are unchanged. No universe checking is
disabled. The fixture is now included in the maintained targeted kernel list.

## Scope and validation

Source modules: **449 → 436**. Regression modules: **119 → 105**.
Python tools: **20 → 20**. Markdown documents under `docs`: **66 → 67**
(this inventory is the one addition).
The change is intentionally more conservative than a 15–30-file target: file
count is not evidence of redundant coverage. The independent compilation units
and maintained internal-proof clients account for much of the retained tree.

The existing current-tree audits are reused. There is no new historical replay
audit or snapshot-update mode. Contract changes are declaration-path relocation
and removal of sixteen regression entries (fifteen bare aliases and the duplicate
bind client). Apart from the explicit fixture eta-expansion above, retained
endpoint types match after namespace/pretty-print changes; logical assumptions
are unchanged. Source-policy entries
follow moved/merged tests, and `AllImports` still excludes Gate M.

Local verification of the resulting tree:

- Full `opam exec -- dune build`, including safe AllImports and the separately
  allowlisted Gate M files. A full build is not a universe-safe claim for Gate M.
- Current architecture, source-soundness and public-surface checks; 143 Python
  tool tests. No new historical audit tool.
- All 34 compiled-contract groups passed on the final tree: 27 Gate S groups
  (1587 entries) and 7 separately queried Gate M groups (76 entries), including
  the cause-sensitive iteration-universe negative probe.
- Central 465-entry and MathComp contract snapshot files are byte-identical
  to the baseline. The themed snapshots remove only sixteen regression entries
  and apply the explicit relocations/fixture correction above; no new logical
  axiom is allowed.
- One-off review: all 302 existing Core/Eq/Prob/Interp/Semantics/Execution
  source files are byte-identical. The 1242 retained proved regression declarations
  keep their proofs, modulo namespace relocation; the runner statements also
  receive the documented native-functor eta expansion.
- Joint `coqchk -norec` passed for ten safe module bodies: `FiniteLists`,
  `IterationFrontiers`, `Runner`, `RationalSampling`, internal `Kernel`,
  `MDPEncoding`, `FreeOmegaOrder`, `RealSamplingHandler`, `MathCompUniverse`,
  and `AllImports`. Compiled dependencies were trusted, not recursively
  rechecked; Gate M was excluded. The earlier failed runner check is described
  above and is not counted as a pass.
- CI was deliberately not queried or modified.

The inventory below records every baseline regression's disposition. Paths omit
`theories/` and `.v`; **KEEP** means the same file, **MOVE** changes its owner or
category, **MERGE** retains its current contracts in a thematic module, and
**DELETE** removes only the historical certificate. The deletion details above
apply within merged files; MERGE does not mean deleting the behavioral tests.

## Baseline file inventory

<!-- inventory generated from the reviewed move/merge list -->

| Baseline module | Action | Current module |
|---|---|---|
| `Regression/Backend/BackendCapabilities` | KEEP | `Regression/Backend/BackendCapabilities` |
| `Regression/Backend/CouplingRealization` | KEEP | `Regression/Backend/CouplingRealization` |
| `Regression/Backend/EnumQMeasureRegression` | KEEP | `Regression/Backend/EnumQMeasureRegression` |
| `Regression/Backend/ExtendedEnumQ` | KEEP | `Regression/Backend/ExtendedEnumQ` |
| `Regression/Backend/FiniteBackendConsolidation` | MERGE | `Regression/Backend/FiniteLists` |
| `Regression/Backend/FiniteSupport` | KEEP | `Regression/Backend/FiniteSupport` |
| `Regression/Backend/FreeOmegaEscapingMass` | MOVE | `Regression/Probability/FreeOmegaEscapingMass` |
| `Regression/Backend/FreeOmegaLimitSafety` | MOVE | `Regression/Probability/FreeOmegaLimitSafety` |
| `Regression/Backend/FreeOmegaUpperContracts` | MOVE | `Regression/Probability/FreeOmegaUpperContracts` |
| `Regression/Backend/MathComp` | KEEP | `Regression/Backend/MathComp` |
| `Regression/Backend/MathCompOmega` | KEEP | `Regression/Backend/MathCompOmega` |
| `Regression/Backend/MathCompOrder` | KEEP | `Regression/Backend/MathCompOrder` |
| `Regression/Backend/NativeReflection` | KEEP | `Regression/Backend/NativeReflection` |
| `Regression/Backend/RationalFiniteAlgebra` | MERGE | `Regression/Backend/FiniteLists` |
| `Regression/Backend/RationalPositions` | MERGE | `Regression/Backend/FiniteLists` |
| `Regression/Backend/RationalPresentation` | MERGE | `Regression/Backend/FiniteLists` |
| `Regression/Backend/RationalPruning` | MERGE | `Regression/Backend/FiniteLists` |
| `Regression/Backend/RationalReplay` | MERGE | `Regression/Execution/RationalSampling` |
| `Regression/Backend/RationalRepresentationMigration` | DELETE | — |
| `Regression/Backend/SubEnumQRegression` | KEEP | `Regression/Backend/SubEnumQRegression` |
| `Regression/Backend/SubEnumR` | KEEP | `Regression/Backend/SubEnumR` |
| `Regression/Backend/SubEnumRBehavior` | KEEP | `Regression/Backend/SubEnumRBehavior` |
| `Regression/Backend/SubEnumRRelational` | KEEP | `Regression/Backend/SubEnumRRelational` |
| `Regression/Backend/SubEnumRShared` | KEEP | `Regression/Backend/SubEnumRShared` |
| `Regression/Backend/UnifiedFrontierEnumQ` | KEEP | `Regression/Backend/UnifiedFrontierEnumQ` |
| `Regression/Execution/FactoryController` | KEEP | `Regression/Execution/FactoryController` |
| `Regression/Execution/FiniteDistribution` | KEEP | `Regression/Execution/FiniteDistribution` |
| `Regression/Execution/Outcome` | MERGE | `Regression/Execution/Runner` |
| `Regression/Execution/RationalTickets` | MERGE | `Regression/Execution/RationalSampling` |
| `Regression/Fixtures/FreeOmegaSamples` | KEEP | `Regression/Fixtures/FreeOmegaSamples` |
| `Regression/Infrastructure/AllImports` | KEEP | `Regression/Infrastructure/AllImports` |
| `Regression/Infrastructure/ArchitectureBoundaries` | KEEP | `Regression/Infrastructure/ArchitectureBoundaries` |
| `Regression/Infrastructure/CanonicalBehavior` | MOVE | `Regression/ImportOrder/CanonicalBehavior` |
| `Regression/Infrastructure/CanonicalBehaviorNativeFirst` | MOVE | `Regression/ImportOrder/CanonicalBehaviorNativeFirst` |
| `Regression/Infrastructure/CanonicalBehaviorStructuralFirst` | MOVE | `Regression/ImportOrder/CanonicalBehaviorStructuralFirst` |
| `Regression/Infrastructure/CapabilityBoundaries` | KEEP | `Regression/Infrastructure/CapabilityBoundaries` |
| `Regression/Infrastructure/CorrelatedInternalRounds` | MOVE | `Regression/Internal/CorrelatedInternalRounds` |
| `Regression/Infrastructure/CostedRounds` | MOVE | `Regression/Internal/CostedRounds` |
| `Regression/Infrastructure/CouplingReferences` | MOVE | `Regression/Internal/CouplingReferences` |
| `Regression/Infrastructure/Execution` | MERGE | `Regression/Execution/Runner` |
| `Regression/Infrastructure/FiniteInternalNative` | MOVE | `Regression/Internal/FiniteInternalNative` |
| `Regression/Infrastructure/FiniteInternalPlan` | MOVE | `Regression/Internal/FiniteInternalPlan` |
| `Regression/Infrastructure/FiniteInternalRound` | MOVE | `Regression/Internal/FiniteInternalRound` |
| `Regression/Infrastructure/HiddenRandomState` | MOVE | `Regression/Internal/HiddenRandomState` |
| `Regression/Infrastructure/KernelCompletion` | MERGE | `Regression/Internal/Kernel` |
| `Regression/Infrastructure/KernelCongruence` | MERGE | `Regression/Internal/Kernel` |
| `Regression/Infrastructure/KernelContinuity` | MERGE | `Regression/Internal/Kernel` |
| `Regression/Infrastructure/MathCompUniverse` | KEEP | `Regression/Infrastructure/MathCompUniverse` |
| `Regression/Infrastructure/NativeRecovery` | MOVE | `Regression/Internal/NativeRecovery` |
| `Regression/Infrastructure/PairedFiniteCompression` | MOVE | `Regression/Internal/PairedFiniteCompression` |
| `Regression/Infrastructure/PublicBehavior` | KEEP | `Regression/Infrastructure/PublicBehavior` |
| `Regression/Infrastructure/PublicHandlers` | KEEP | `Regression/Infrastructure/PublicHandlers` |
| `Regression/Infrastructure/ResidualFinite` | MOVE | `Regression/Internal/ResidualFinite` |
| `Regression/Infrastructure/ResidualJointCoinduction` | MOVE | `Regression/Internal/ResidualJointCoinduction` |
| `Regression/Infrastructure/ResidualTransport` | MOVE | `Regression/Internal/ResidualTransport` |
| `Regression/Infrastructure/StateIteration` | MOVE | `Regression/Execution/StateIteration` |
| `Regression/Infrastructure/StructuralRegistry` | KEEP | `Regression/Infrastructure/StructuralRegistry` |
| `Regression/Infrastructure/UniverseSeparatedPTree` | KEEP | `Regression/Infrastructure/UniverseSeparatedPTree` |
| `Regression/Probability/ConditionalResampling` | KEEP | `Regression/Probability/ConditionalResampling` |
| `Regression/Probability/CorrelatedSampleAlgebra` | KEEP | `Regression/Probability/CorrelatedSampleAlgebra` |
| `Regression/Probability/CountableCoupling` | KEEP | `Regression/Probability/CountableCoupling` |
| `Regression/Probability/EnumQDisintegration` | KEEP | `Regression/Probability/EnumQDisintegration` |
| `Regression/Probability/FiniteRepresentation` | KEEP | `Regression/Probability/FiniteRepresentation` |
| `Regression/Probability/FiniteTransport` | KEEP | `Regression/Probability/FiniteTransport` |
| `Regression/Probability/FreeOmegaDomain` | KEEP | `Regression/Probability/FreeOmegaDomain` |
| `Regression/Probability/FreeOmegaSoundness` | KEEP | `Regression/Probability/FreeOmegaSoundness` |
| `Regression/Probability/GenericFreeOmegaValidation` | KEEP | `Regression/Probability/GenericFreeOmegaValidation` |
| `Regression/Probability/GenericQuotientValidation` | KEEP | `Regression/Probability/GenericQuotientValidation` |
| `Regression/Probability/IrrationalHitting` | KEEP | `Regression/Probability/IrrationalHitting` |
| `Regression/Probability/KleisliIteration` | KEEP | `Regression/Probability/KleisliIteration` |
| `Regression/Probability/OmegaVal` | KEEP | `Regression/Probability/OmegaVal` |
| `Regression/Probability/OmegaValMeasure` | KEEP | `Regression/Probability/OmegaValMeasure` |
| `Regression/Probability/RealTransport` | KEEP | `Regression/Probability/RealTransport` |
| `Regression/Probability/RelationalLimit` | KEEP | `Regression/Probability/RelationalLimit` |
| `Regression/Probability/StableHittingDomain` | KEEP | `Regression/Probability/StableHittingDomain` |
| `Regression/Probability/SubEnumRJointRealization` | KEEP | `Regression/Probability/SubEnumRJointRealization` |
| `Regression/Probability/SubEnumRNativeReflection` | KEEP | `Regression/Probability/SubEnumRNativeReflection` |
| `Regression/Semantics/AbsorbingIteration` | MERGE | `Regression/Semantics/IterationFrontiers` |
| `Regression/Semantics/AtomicInterp` | KEEP | `Regression/Semantics/AtomicInterp` |
| `Regression/Semantics/CanonicalPartialDivergence` | KEEP | `Regression/Semantics/CanonicalPartialDivergence` |
| `Regression/Semantics/EffectAlgebra` | KEEP | `Regression/Semantics/EffectAlgebra` |
| `Regression/Semantics/EventfulIteration` | KEEP | `Regression/Semantics/EventfulIteration` |
| `Regression/Semantics/ExceptionFold` | KEEP | `Regression/Semantics/ExceptionFold` |
| `Regression/Semantics/FreeOmegaRewriting` | KEEP | `Regression/Semantics/FreeOmegaRewriting` |
| `Regression/Semantics/FrontierIteration` | MERGE | `Regression/Semantics/IterationFrontiers` |
| `Regression/Semantics/GenericAlgebra` | KEEP | `Regression/Semantics/GenericAlgebra` |
| `Regression/Semantics/GenericBind` | MOVE | `Regression/Probability/FreeOmegaOrder` |
| `Regression/Semantics/GenericConsumers` | KEEP | `Regression/Semantics/GenericConsumers` |
| `Regression/Semantics/GuardedInterp` | KEEP | `Regression/Semantics/GuardedInterp` |
| `Regression/Semantics/HandlerCalculus` | MOVE | `Examples/RealSamplingHandler` |
| `Regression/Semantics/HeadTransition` | KEEP | `Regression/Semantics/HeadTransition` |
| `Regression/Semantics/ITreeBridge` | KEEP | `Regression/Semantics/ITreeBridge` |
| `Regression/Semantics/ITreePreservation` | KEEP | `Regression/Semantics/ITreePreservation` |
| `Regression/Semantics/InterpExposure` | KEEP | `Regression/Semantics/InterpExposure` |
| `Regression/Semantics/IterationSummary` | MERGE | `Regression/Semantics/IterationFrontiers` |
| `Regression/Semantics/LabelledMDP` | MERGE | `Regression/Semantics/MDPEncoding` |
| `Regression/Semantics/MDPCoincidence` | KEEP | `Regression/Semantics/MDPCoincidence` |
| `Regression/Semantics/MDPEmbedding` | MERGE | `Regression/Semantics/MDPEncoding` |
| `Regression/Semantics/MDPFragment` | KEEP | `Regression/Semantics/MDPFragment` |
| `Regression/Semantics/MDPInterp` | KEEP | `Regression/Semantics/MDPInterp` |
| `Regression/Semantics/OperationalPTSExamples` | MOVE | `Regression/Semantics/HittingPrograms` |
| `Regression/Semantics/PEuttAlgebra` | KEEP | `Regression/Semantics/PEuttAlgebra` |
| `Regression/Semantics/PTreeIterationAlgebra` | KEEP | `Regression/Semantics/PTreeIterationAlgebra` |
| `Regression/Semantics/PTreeUniformity` | KEEP | `Regression/Semantics/PTreeUniformity` |
| `Regression/Semantics/ProbabilisticRelationHierarchy` | KEEP | `Regression/Semantics/ProbabilisticRelationHierarchy` |
| `Regression/Semantics/PublicSemanticFacade` | KEEP | `Regression/Semantics/PublicSemanticFacade` |
| `Regression/Semantics/ReaderWriterFold` | KEEP | `Regression/Semantics/ReaderWriterFold` |
| `Regression/Semantics/RelationalConsumers` | KEEP | `Regression/Semantics/RelationalConsumers` |
| `Regression/Semantics/ReturnIteration` | MERGE | `Regression/Semantics/IterationFrontiers` |
| `Regression/Semantics/StableHittingComputation` | KEEP | `Regression/Semantics/StableHittingComputation` |
| `Regression/Semantics/StandardEffects` | KEEP | `Regression/Semantics/StandardEffects` |
| `Regression/Semantics/StateFold` | KEEP | `Regression/Semantics/StateFold` |
| `Regression/Semantics/StatePreservation` | KEEP | `Regression/Semantics/StatePreservation` |
| `Regression/Semantics/TreeTransition` | KEEP | `Regression/Semantics/TreeTransition` |
| `Regression/Semantics/TreeTransitionBisim` | KEEP | `Regression/Semantics/TreeTransitionBisim` |
| `Regression/Semantics/TreeTransitionSoundness` | KEEP | `Regression/Semantics/TreeTransitionSoundness` |
| `Regression/Semantics/TreeTransitionStrictness` | KEEP | `Regression/Semantics/TreeTransitionStrictness` |
| `Regression/Semantics/UnrestrictedInterp` | KEEP | `Regression/Semantics/UnrestrictedInterp` |
| `Regression/Semantics/UpToProb` | KEEP | `Regression/Semantics/UpToProb` |
