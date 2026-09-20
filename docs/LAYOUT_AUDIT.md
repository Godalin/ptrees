# Structural layout audit

This is a repository-local dependency audit, not a theorem-usage or external-client census. It separately verifies historical layout invariance and reports current clients.

Regenerate with `python3 tools/audit_layout.py` after a full `opam exec -- dune build`. The read-only proof-text check is pinned to the layout snapshot, not later reviewed fixes.

## Scope and invariance

- Layout comparison: `92e0841` -> `6194bdf`; 190 Coq modules before and after; 65 moves; zero theorem/module deletions.
- Between those snapshots all definition, theorem-statement and proof text is identical after normalizing Require paths; the only other Coq edit updates one comment's regression path.
- In that historical snapshot all nine `Semantics/` modules and all finite-internal/kernel implementations remained in place. The later [Gate B migration](ARCHITECTURE_MIGRATION.md) relocates modules; current client paths below include those moves.
- [Complete file move manifest](module-moves.tsv): each row also determines the old/new qualified module name; file basenames and declaration names are unchanged. No compatibility wrapper modules were added.
- Classification: 15 files in four case-study groups; 50 regressions (17 semantics, 14 backend, 4 probability, 15 infrastructure). Factory contains ordinary Von Neumann support shared by the interactive service.
- The later [universe repair](UNIVERSE_CONSISTENCY.md) updates two old Enum/Enum regressions and adds one import-only integration harness; it is not asserted to be a namespace-only change.
- The layout milestone introduced no final MDP-encoding transition corollary or new semantic theorem; later theory work is recorded in [THEORY_STATUS](../THEORY_STATUS.md).

## Dependency method and retained roots

Coq's `.PTree.theory.d` supplies 1831 direct local Require edges covering 207 ordinary modules out of 208 maintained modules. External libraries are excluded. Transitive clients include re-export paths; an import does not prove use of each declaration.

`AllImports` is checked to import every other module, then excluded from client/reachability counts: an integration harness must not make every otherwise-unused module look substantively live.

Checked layer boundaries: Core/Prob/Eq/Semantics/Interp/API import no case study or regression; case studies import no regression. Regression-to-case-study reuse is allowed.

Roots are every Core module, every semantic comparison module, the API/Interp modules and top-level facades, the structural/strong and FreeOmega equational endpoints, both concrete trace probability endpoints, and all four retained case-study groups. This deliberately does not treat every regression as a public root.

`PTree.API.Enum`, `PTree.API.FreeOmega`, `PTree.API.Generic`, `PTree.API.SubEnum`, `PTree.API.Weighted`, `PTree.CaseStudies.BernoulliFactory.BernoulliFactory`, `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryComposition`, `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryProbability`, `PTree.CaseStudies.BernoulliFactory.OperationalBernoulliFactory`, `PTree.CaseStudies.BernoulliFactory.OperationalRationalBernoulli`, `PTree.CaseStudies.BernoulliFactory.OperationalRealBernoulliMathComp`, `PTree.CaseStudies.BernoulliFactory.OperationalVonNeumann`, `PTree.CaseStudies.BernoulliFactory.RationalBernoulli`, `PTree.CaseStudies.BernoulliFactory.RealBernoulliMathComp`, `PTree.CaseStudies.BernoulliFactory.RealBernoulliOracle`, `PTree.CaseStudies.BernoulliFactory.UnifiedRealBernoulliMathCompCore`, `PTree.CaseStudies.BernoulliFactory.VonNeumannUnbounded`, `PTree.CaseStudies.InteractiveVonNeumann.InteractiveVonNeumannService`, `PTree.CaseStudies.MixedHeadProtocol`, `PTree.CaseStudies.RandomWalk`, `PTree.Core.PTreeDefinition`, `PTree.Core.Utils`, `PTree.Eq.Backend.ProbabilisticTraceEnum`, `PTree.Eq.Backend.ProbabilisticTraceSubEnum`, `PTree.Eq.PStrong`, `PTree.Eq.PStruct`, `PTree.Interp.Backend.SubEnum`, `PTree.Interp.FreeOmega.Atomic`, `PTree.Interp.FreeOmega.Base`, `PTree.Interp.FreeOmega.Cofinality`, `PTree.Interp.FreeOmega.Guarded`, `PTree.Interp.FreeOmega.MDP`, `PTree.Interp.FreeOmega.Translate`, `PTree.Interp.Kernel`, `PTree.Interp.Structural`, `PTree.PTree`, `PTree.Semantics`, `PTree.Semantics.Backend.MDPEmbeddingSubEnum`, `PTree.Semantics.FreeOmega.MDPCoincidenceFreeOmega`, `PTree.Semantics.HeadTransition`, `PTree.Semantics.MDPCoincidence`, `PTree.Semantics.MDPEmbedding`, `PTree.Semantics.MDPFragment`, `PTree.Semantics.TreeTransition`, `PTree.Semantics.TreeTransitionBisim`, `PTree.Semantics.TreeTransitionSoundness`

Root closure reaches 105 modules; 102 lie outside it. Unreachable modules can still be meaningful regressions or independent measure theorems. All remain built by Dune; no deletion follows from this classification.

### Outside the selected root closure

- `PTree.Eq.Backend.EnumCofinality` (0 direct local clients)
- `PTree.Eq.Internal.Backend.KernelDisintegration` (1 direct local clients)
- `PTree.Eq.Internal.FiniteInternal` (24 direct local clients)
- `PTree.Eq.Internal.FiniteInternalHitting` (3 direct local clients)
- `PTree.Eq.Internal.FiniteInternalJoint` (1 direct local clients)
- `PTree.Eq.Internal.FiniteInternalPlan` (14 direct local clients)
- `PTree.Eq.Internal.FreeOmega.CostedKernel` (4 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternal` (4 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalAcceleration` (4 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction` (2 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection` (4 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalJoint` (13 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration` (2 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction` (1 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage` (3 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalJointHitting` (3 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference` (2 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows` (1 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation` (1 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalNative` (12 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalNativeJoint` (2 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalPlanHitting` (2 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy` (1 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalRound` (6 direct local clients)
- `PTree.Eq.Internal.FreeOmega.FiniteInternalRoundCoupling` (4 direct local clients)
- `PTree.Eq.Internal.FreeOmega.KernelCompletion` (11 direct local clients)
- `PTree.Eq.Internal.FreeOmega.KernelCongruence` (4 direct local clients)
- `PTree.Eq.Internal.FreeOmega.KernelContinuity` (4 direct local clients)
- `PTree.Eq.Internal.FreeOmega.KernelProjection` (2 direct local clients)
- `PTree.Prob.Backend.FinSupp` (0 direct local clients)
- `PTree.Prob.Backend.FreeOmega.FreeOmegaCodedJointSubEnum` (1 direct local clients)
- `PTree.Prob.Backend.FreeOmega.FreeOmegaCouplingEnum` (3 direct local clients)
- `PTree.Prob.Backend.FreeOmega.FreeOmegaEquivalenceJointSubEnum` (1 direct local clients)
- `PTree.Prob.Backend.FreeOmega.FreeOmegaMeasureEnumAudit` (0 direct local clients)
- `PTree.Prob.Backend.FreeOmega.FreeOmegaNativeTransportEnum` (0 direct local clients)
- `PTree.Prob.Backend.FreeOmega.FreeOmegaUpperContinuityEnum` (3 direct local clients)
- `PTree.Prob.Backend.FreeOmega.FreeOmegaUpperCouplingEnum` (5 direct local clients)
- `PTree.Prob.Backend.FreeOmega.FreeOmegaUpperExpectationEnum` (8 direct local clients)
- `PTree.Prob.Backend.FreeOmega.FreeOmegaUpperObservationEnum` (2 direct local clients)
- `PTree.Prob.Backend.FreeOmega.FreeOmegaUpperQuotientEnum` (2 direct local clients)
- `PTree.Prob.Backend.FreeOmega.FreeOmegaUpperRelationalEnum` (2 direct local clients)
- `PTree.Prob.Backend.RealSubTypes` (1 direct local clients)
- `PTree.Prob.Backend.SemanticCouplingMathComp` (1 direct local clients)
- `PTree.Prob.FreeOmega.FreeOmegaJointExtension` (2 direct local clients)
- `PTree.Prob.Legacy.Discrete` (0 direct local clients)
- `PTree.Prob.Legacy.MonadList` (0 direct local clients)
- `PTree.Regression.Backend.BackendCapabilities` (0 direct local clients)
- `PTree.Regression.Backend.CouplingRealization` (0 direct local clients)
- `PTree.Regression.Backend.EnumMeasureRegression` (12 direct local clients)
- `PTree.Regression.Backend.ExtendedEnum` (0 direct local clients)
- `PTree.Regression.Backend.FreeOmegaEscapingMass` (4 direct local clients)
- `PTree.Regression.Backend.FreeOmegaLimitSafety` (0 direct local clients)
- `PTree.Regression.Backend.FreeOmegaUpperContinuity` (0 direct local clients)
- `PTree.Regression.Backend.FreeOmegaUpperExpectation` (2 direct local clients)
- `PTree.Regression.Backend.FreeOmegaUpperObservation` (1 direct local clients)
- `PTree.Regression.Backend.FreeOmegaUpperQuotient` (0 direct local clients)
- `PTree.Regression.Backend.NativeReflection` (0 direct local clients)
- `PTree.Regression.Backend.SubEnumRegression` (17 direct local clients)
- `PTree.Regression.Backend.UnifiedFrontierEnum` (0 direct local clients)
- `PTree.Regression.Backend.UnifiedMathCompFrontier` (0 direct local clients)
- `PTree.Regression.Infrastructure.ArchitectureBoundaries` (0 direct local clients)
- `PTree.Regression.Infrastructure.CorrelatedInternalRounds` (0 direct local clients)
- `PTree.Regression.Infrastructure.CostedRounds` (0 direct local clients)
- `PTree.Regression.Infrastructure.CouplingReferences` (3 direct local clients)
- `PTree.Regression.Infrastructure.FiniteInternalNative` (0 direct local clients)
- `PTree.Regression.Infrastructure.FiniteInternalPlan` (3 direct local clients)
- `PTree.Regression.Infrastructure.FiniteInternalRound` (0 direct local clients)
- `PTree.Regression.Infrastructure.HiddenRandomState` (2 direct local clients)
- `PTree.Regression.Infrastructure.KernelCompletion` (0 direct local clients)
- `PTree.Regression.Infrastructure.KernelCongruence` (0 direct local clients)
- `PTree.Regression.Infrastructure.KernelContinuity` (0 direct local clients)
- `PTree.Regression.Infrastructure.NativeRecovery` (0 direct local clients)
- `PTree.Regression.Infrastructure.PairedFiniteCompression` (1 direct local clients)
- `PTree.Regression.Infrastructure.ResidualFinite` (2 direct local clients)
- `PTree.Regression.Infrastructure.ResidualJointCoinduction` (0 direct local clients)
- `PTree.Regression.Infrastructure.ResidualTransport` (0 direct local clients)
- `PTree.Regression.Infrastructure.UniverseSeparatedPTree` (0 direct local clients)
- `PTree.Regression.Probability.ConditionalResampling` (0 direct local clients)
- `PTree.Regression.Probability.CorrelatedSampleAlgebra` (4 direct local clients)
- `PTree.Regression.Probability.EnumDisintegration` (1 direct local clients)
- `PTree.Regression.Probability.FiniteTransport` (0 direct local clients)
- `PTree.Regression.Semantics.AtomicInterp` (1 direct local clients)
- `PTree.Regression.Semantics.CanonicalPartialDivergence` (0 direct local clients)
- `PTree.Regression.Semantics.GuardedInterp` (0 direct local clients)
- `PTree.Regression.Semantics.HeadTransition` (0 direct local clients)
- `PTree.Regression.Semantics.HittingDivergence` (0 direct local clients)
- `PTree.Regression.Semantics.InterpExposure` (2 direct local clients)
- `PTree.Regression.Semantics.LabelledMDP` (0 direct local clients)
- `PTree.Regression.Semantics.MDPCoincidence` (1 direct local clients)
- `PTree.Regression.Semantics.MDPEmbedding` (0 direct local clients)
- `PTree.Regression.Semantics.MDPFragment` (2 direct local clients)
- `PTree.Regression.Semantics.MDPInterp` (0 direct local clients)
- `PTree.Regression.Semantics.OperationalPTSExamples` (0 direct local clients)
- `PTree.Regression.Semantics.PEuttAlgebra` (2 direct local clients)
- `PTree.Regression.Semantics.PEuttNotation` (0 direct local clients)
- `PTree.Regression.Semantics.ProbabilisticRelationHierarchy` (0 direct local clients)
- `PTree.Regression.Semantics.PublicSemanticFacade` (0 direct local clients)
- `PTree.Regression.Semantics.StableHittingComputation` (0 direct local clients)
- `PTree.Regression.Semantics.TreeTransition` (2 direct local clients)
- `PTree.Regression.Semantics.TreeTransitionBisim` (0 direct local clients)
- `PTree.Regression.Semantics.TreeTransitionSoundness` (0 direct local clients)
- `PTree.Regression.Semantics.TreeTransitionStrictness` (4 direct local clients)

### Zero direct local clients (report only)

50 modules have no direct local client. This includes exported roots and executable/negative regression leaves, not just potential dead code.

- `PTree.API.SubEnum` — retained root
- `PTree.API.Weighted` — retained root
- `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryComposition` — retained root
- `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryProbability` — retained root
- `PTree.CaseStudies.BernoulliFactory.OperationalRationalBernoulli` — retained root
- `PTree.CaseStudies.BernoulliFactory.OperationalRealBernoulliMathComp` — retained root
- `PTree.CaseStudies.MixedHeadProtocol` — retained root
- `PTree.Eq.Backend.EnumCofinality` — built leaf
- `PTree.Prob.Backend.FinSupp` — built leaf
- `PTree.Prob.Backend.FreeOmega.FreeOmegaMeasureEnumAudit` — built leaf
- `PTree.Prob.Backend.FreeOmega.FreeOmegaNativeTransportEnum` — built leaf
- `PTree.Prob.Legacy.Discrete` — built leaf
- `PTree.Prob.Legacy.MonadList` — built leaf
- `PTree.Regression.Backend.BackendCapabilities` — built leaf
- `PTree.Regression.Backend.CouplingRealization` — built leaf
- `PTree.Regression.Backend.ExtendedEnum` — built leaf
- `PTree.Regression.Backend.FreeOmegaLimitSafety` — built leaf
- `PTree.Regression.Backend.FreeOmegaUpperContinuity` — built leaf
- `PTree.Regression.Backend.FreeOmegaUpperQuotient` — built leaf
- `PTree.Regression.Backend.NativeReflection` — built leaf
- `PTree.Regression.Backend.UnifiedFrontierEnum` — built leaf
- `PTree.Regression.Backend.UnifiedMathCompFrontier` — built leaf
- `PTree.Regression.Infrastructure.ArchitectureBoundaries` — built leaf
- `PTree.Regression.Infrastructure.CorrelatedInternalRounds` — built leaf
- `PTree.Regression.Infrastructure.CostedRounds` — built leaf
- `PTree.Regression.Infrastructure.FiniteInternalNative` — built leaf
- `PTree.Regression.Infrastructure.FiniteInternalRound` — built leaf
- `PTree.Regression.Infrastructure.KernelCompletion` — built leaf
- `PTree.Regression.Infrastructure.KernelCongruence` — built leaf
- `PTree.Regression.Infrastructure.KernelContinuity` — built leaf
- `PTree.Regression.Infrastructure.NativeRecovery` — built leaf
- `PTree.Regression.Infrastructure.ResidualJointCoinduction` — built leaf
- `PTree.Regression.Infrastructure.ResidualTransport` — built leaf
- `PTree.Regression.Infrastructure.UniverseSeparatedPTree` — built leaf
- `PTree.Regression.Probability.ConditionalResampling` — built leaf
- `PTree.Regression.Probability.FiniteTransport` — built leaf
- `PTree.Regression.Semantics.CanonicalPartialDivergence` — built leaf
- `PTree.Regression.Semantics.GuardedInterp` — built leaf
- `PTree.Regression.Semantics.HeadTransition` — built leaf
- `PTree.Regression.Semantics.HittingDivergence` — built leaf
- `PTree.Regression.Semantics.LabelledMDP` — built leaf
- `PTree.Regression.Semantics.MDPEmbedding` — built leaf
- `PTree.Regression.Semantics.MDPInterp` — built leaf
- `PTree.Regression.Semantics.OperationalPTSExamples` — built leaf
- `PTree.Regression.Semantics.PEuttNotation` — built leaf
- `PTree.Regression.Semantics.ProbabilisticRelationHierarchy` — built leaf
- `PTree.Regression.Semantics.PublicSemanticFacade` — built leaf
- `PTree.Regression.Semantics.StableHittingComputation` — built leaf
- `PTree.Regression.Semantics.TreeTransitionBisim` — built leaf
- `PTree.Regression.Semantics.TreeTransitionSoundness` — built leaf

## Finite-internal / kernel family: complete local client report

Scope: every `Eq/**/FiniteInternal*.v`, plus FreeOmega KernelCompletion, KernelCongruence, KernelProjection, KernelDisintegration, KernelContinuity and CostedKernel. Incoming/outgoing direct lists and transitive client lists are exhaustive within `theories/`. Gate B moved this family under Eq/Internal, updating all clients together. No dead-code conclusion follows from historical names.

### `PTree.Eq.Internal.Backend.KernelDisintegration`

- In retained-root closure: no.
- Direct imports: `PTree.Eq.Internal.FreeOmega.KernelCompletion`, `PTree.Eq.Internal.FreeOmega.KernelCongruence`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Prob.Backend.EnumDisintegration`, `PTree.Prob.Backend.FreeOmega.FreeOmegaDisintegration`, `PTree.Prob.Backend.TwoLevelMeasureSubEnum`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Regression.Probability.ConditionalResampling`.
- All transitive clients: `PTree.Regression.Probability.ConditionalResampling`.

### `PTree.Eq.Internal.FiniteInternal`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FiniteInternalHitting`, `PTree.Eq.Internal.FiniteInternalJoint`, `PTree.Eq.Internal.FiniteInternalPlan`, `PTree.Eq.Internal.FreeOmega.FiniteInternal`, `PTree.Eq.Internal.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNative`, `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.PairedFiniteCompression`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`.
- All transitive clients: `PTree.Eq.Internal.FiniteInternalHitting`, `PTree.Eq.Internal.FiniteInternalJoint`, `PTree.Eq.Internal.FiniteInternalPlan`, `PTree.Eq.Internal.FreeOmega.FiniteInternal`, `PTree.Eq.Internal.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNative`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNativeJoint`, `PTree.Eq.Internal.FreeOmega.FiniteInternalPlanHitting`, `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRound`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.PairedFiniteCompression`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.AtomicInterp`, `PTree.Regression.Semantics.GuardedInterp`, `PTree.Regression.Semantics.InterpExposure`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.MDPInterp`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.Internal.FiniteInternalHitting`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternal`, `PTree.Eq.PEutt`, `PTree.Eq.PStrong`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FiniteInternalJoint`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointHitting`, `PTree.Regression.Infrastructure.ResidualFinite`.
- All transitive clients: `PTree.Eq.Internal.FiniteInternalJoint`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.PairedFiniteCompression`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.AtomicInterp`, `PTree.Regression.Semantics.GuardedInterp`, `PTree.Regression.Semantics.InterpExposure`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.MDPInterp`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.Internal.FiniteInternalJoint`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternal`, `PTree.Eq.Internal.FiniteInternalHitting`, `PTree.Eq.PStrong`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.Interface.SemanticCoupling`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Regression.Infrastructure.PairedFiniteCompression`.
- All transitive clients: `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.PairedFiniteCompression`.

### `PTree.Eq.Internal.FiniteInternalPlan`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternal`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNative`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNativeJoint`, `PTree.Eq.Internal.FreeOmega.FiniteInternalPlanHitting`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRound`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.NativeRecovery`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNative`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNativeJoint`, `PTree.Eq.Internal.FreeOmega.FiniteInternalPlanHitting`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRound`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.Internal.FreeOmega.CostedKernel`

- In retained-root closure: no.
- Direct imports: `PTree.Eq.Internal.FreeOmega.KernelContinuity`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternal`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternal`, `PTree.Eq.PStrong`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.AtomicInterp`, `PTree.Regression.Semantics.GuardedInterp`, `PTree.Regression.Semantics.InterpExposure`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.MDPInterp`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalAcceleration`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternal`, `PTree.Eq.Internal.FreeOmega.FiniteInternal`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJoint`, `PTree.Eq.Internal.FreeOmega.KernelContinuity`, `PTree.Eq.PEutt`, `PTree.Eq.PStrong`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaCoupling`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.SemanticCoupling`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternalPlan`, `PTree.Eq.Internal.FreeOmega.CostedKernel`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNative`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRound`, `PTree.Eq.PEutt`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.FreeOmega.FreeOmegaNative`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Infrastructure.CostedRounds`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternalPlan`, `PTree.Eq.Internal.FreeOmega.CostedKernel`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNative`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRound`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.FreeOmega.FreeOmegaNative`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalJoint`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.PStrong`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaCoupling`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.SemanticCoupling`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNative`, `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNative`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNativeJoint`, `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRound`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.AtomicInterp`, `PTree.Regression.Semantics.GuardedInterp`, `PTree.Regression.Semantics.InterpExposure`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.MDPInterp`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternal`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJoint`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.Internal.FreeOmega.KernelCompletion`, `PTree.Eq.Internal.FreeOmega.KernelCongruence`, `PTree.Eq.Internal.FreeOmega.KernelContinuity`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.SemanticCoupling`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.AtomicInterp`, `PTree.Regression.Semantics.GuardedInterp`, `PTree.Regression.Semantics.InterpExposure`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.MDPInterp`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternal`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJoint`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.PEutt`, `PTree.Eq.PStrong`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.SemanticCoupling`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Regression.Infrastructure.CorrelatedInternalRounds`.
- All transitive clients: `PTree.Regression.Infrastructure.CorrelatedInternalRounds`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternal`, `PTree.Eq.Internal.FreeOmega.FiniteInternal`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJoint`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.Internal.FreeOmega.KernelCompletion`, `PTree.Eq.Internal.FreeOmega.KernelCongruence`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.AtomicInterp`, `PTree.Regression.Semantics.GuardedInterp`, `PTree.Regression.Semantics.InterpExposure`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.MDPInterp`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalJointHitting`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternal`, `PTree.Eq.Internal.FiniteInternalHitting`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJoint`, `PTree.Eq.Internal.FreeOmega.KernelCompletion`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.AtomicInterp`, `PTree.Regression.Semantics.GuardedInterp`, `PTree.Regression.Semantics.InterpExposure`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.MDPInterp`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternal`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJoint`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.PEutt`, `PTree.Eq.PStrong`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaCoupling`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.SemanticCoupling`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.AtomicInterp`, `PTree.Regression.Semantics.GuardedInterp`, `PTree.Regression.Semantics.InterpExposure`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.MDPInterp`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternalPlan`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNative`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRound`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Eq.PEutt`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.FreeOmega.FreeOmegaNative`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Regression.Infrastructure.NativeRecovery`.
- All transitive clients: `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternal`, `PTree.Eq.Internal.FreeOmega.FiniteInternal`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJoint`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.SemanticCoupling`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.AtomicInterp`, `PTree.Regression.Semantics.GuardedInterp`, `PTree.Regression.Semantics.InterpExposure`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.MDPInterp`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalNative`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternal`, `PTree.Eq.Internal.FiniteInternalPlan`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJoint`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.FreeOmega.FreeOmegaNative`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNativeJoint`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRound`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.NativeRecovery`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNativeJoint`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRound`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalNativeJoint`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternalPlan`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNative`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Eq.PStrong`, `PTree.Prob.FreeOmega.FreeOmegaJointExtension`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.FreeOmega.FreeOmegaNative`, `PTree.Prob.Interface.SemanticCoupling`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.NativeRecovery`.
- All transitive clients: `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalPlanHitting`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternalPlan`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.FreeOmega.FreeOmegaNative`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalRound`, `PTree.Regression.Infrastructure.FiniteInternalPlan`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.Internal.FreeOmega.FiniteInternalRound`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternal`, `PTree.Eq.Internal.FreeOmega.FiniteInternal`, `PTree.Eq.Internal.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJoint`, `PTree.Eq.Internal.FreeOmega.KernelCompletion`, `PTree.Eq.Internal.FreeOmega.KernelProjection`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Regression.Infrastructure.HiddenRandomState`.
- All transitive clients: `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalRound`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternalPlan`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNative`, `PTree.Eq.Internal.FreeOmega.FiniteInternalPlanHitting`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.FreeOmega.FreeOmegaNative`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalRound`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.Internal.FreeOmega.FiniteInternalRoundCoupling`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.Internal.FiniteInternalPlan`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNative`, `PTree.Eq.PStrong`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.FreeOmega.FreeOmegaNative`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNativeJoint`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.NativeRecovery`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.Internal.FreeOmega.FiniteInternalNativeJoint`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.Internal.FreeOmega.KernelCompletion`

- In retained-root closure: no.
- Direct imports: `PTree.Eq.PrimitiveStableHitting`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.Backend.KernelDisintegration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Eq.Internal.FreeOmega.KernelCongruence`, `PTree.Eq.Internal.FreeOmega.KernelProjection`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.KernelCompletion`, `PTree.Regression.Infrastructure.KernelCongruence`, `PTree.Regression.Probability.ConditionalResampling`.
- All transitive clients: `PTree.Eq.Internal.Backend.KernelDisintegration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Eq.Internal.FreeOmega.KernelCongruence`, `PTree.Eq.Internal.FreeOmega.KernelProjection`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.KernelCompletion`, `PTree.Regression.Infrastructure.KernelCongruence`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.ConditionalResampling`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.AtomicInterp`, `PTree.Regression.Semantics.GuardedInterp`, `PTree.Regression.Semantics.InterpExposure`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.MDPInterp`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.Internal.FreeOmega.KernelCongruence`

- In retained-root closure: no.
- Direct imports: `PTree.Eq.Internal.FreeOmega.KernelCompletion`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.Backend.KernelDisintegration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Regression.Infrastructure.KernelCongruence`.
- All transitive clients: `PTree.Eq.Internal.Backend.KernelDisintegration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointTruncation`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.KernelCongruence`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.ConditionalResampling`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.AtomicInterp`, `PTree.Regression.Semantics.GuardedInterp`, `PTree.Regression.Semantics.InterpExposure`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.MDPInterp`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.Internal.FreeOmega.KernelContinuity`

- In retained-root closure: no.
- Direct imports: `PTree.Eq.PrimitiveStableHitting`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.CostedKernel`, `PTree.Eq.Internal.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Regression.Infrastructure.KernelContinuity`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.CostedKernel`, `PTree.Eq.Internal.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.Internal.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.KernelContinuity`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.AtomicInterp`, `PTree.Regression.Semantics.GuardedInterp`, `PTree.Regression.Semantics.InterpExposure`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.MDPInterp`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.Internal.FreeOmega.KernelProjection`

- In retained-root closure: no.
- Direct imports: `PTree.Eq.Internal.FreeOmega.KernelCompletion`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Prob.FreeOmega.FreeOmegaCoupling`, `PTree.Prob.FreeOmega.FreeOmegaMeasure`, `PTree.Prob.Interface.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.HiddenRandomState`.
- All transitive clients: `PTree.Eq.Internal.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`.

## All changed Require paths

83 imported-module occurrences in 43 client files change namespace.

Each row is one imported module occurrence at the historical layout snapshot (before Gate B). Multi-module statements were split only when their destinations differ, preserving import order.

| Client after move | Previous import | Current import |
| --- | --- | --- |
| `PTree.CaseStudies.BernoulliFactory.BernoulliFactory` | `PTree.Examples.RationalBernoulli` | `PTree.CaseStudies.BernoulliFactory.RationalBernoulli` |
| `PTree.CaseStudies.BernoulliFactory.BernoulliFactory` | `PTree.Examples.VonNeumannUnbounded` | `PTree.CaseStudies.BernoulliFactory.VonNeumannUnbounded` |
| `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryComposition` | `PTree.Examples.BernoulliFactory` | `PTree.CaseStudies.BernoulliFactory.BernoulliFactory` |
| `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryComposition` | `PTree.Examples.OperationalBernoulliFactory` | `PTree.CaseStudies.BernoulliFactory.OperationalBernoulliFactory` |
| `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryComposition` | `PTree.Examples.RationalBernoulli` | `PTree.CaseStudies.BernoulliFactory.RationalBernoulli` |
| `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryComposition` | `PTree.Examples.VonNeumannUnbounded` | `PTree.CaseStudies.BernoulliFactory.VonNeumannUnbounded` |
| `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryProbability` | `PTree.Examples.BernoulliFactory` | `PTree.CaseStudies.BernoulliFactory.BernoulliFactory` |
| `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryProbability` | `PTree.Examples.RationalBernoulli` | `PTree.CaseStudies.BernoulliFactory.RationalBernoulli` |
| `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryProbability` | `PTree.Examples.VonNeumannUnbounded` | `PTree.CaseStudies.BernoulliFactory.VonNeumannUnbounded` |
| `PTree.CaseStudies.BernoulliFactory.OperationalBernoulliFactory` | `PTree.Examples.BernoulliFactory` | `PTree.CaseStudies.BernoulliFactory.BernoulliFactory` |
| `PTree.CaseStudies.BernoulliFactory.OperationalBernoulliFactory` | `PTree.Examples.RationalBernoulli` | `PTree.CaseStudies.BernoulliFactory.RationalBernoulli` |
| `PTree.CaseStudies.BernoulliFactory.OperationalBernoulliFactory` | `PTree.Examples.VonNeumannUnbounded` | `PTree.CaseStudies.BernoulliFactory.VonNeumannUnbounded` |
| `PTree.CaseStudies.BernoulliFactory.OperationalRationalBernoulli` | `PTree.Examples.RationalBernoulli` | `PTree.CaseStudies.BernoulliFactory.RationalBernoulli` |
| `PTree.CaseStudies.BernoulliFactory.OperationalRealBernoulliMathComp` | `PTree.Examples.RealBernoulliMathComp` | `PTree.CaseStudies.BernoulliFactory.RealBernoulliMathComp` |
| `PTree.CaseStudies.BernoulliFactory.OperationalRealBernoulliMathComp` | `PTree.Examples.RealBernoulliOracle` | `PTree.CaseStudies.BernoulliFactory.RealBernoulliOracle` |
| `PTree.CaseStudies.BernoulliFactory.OperationalRealBernoulliMathComp` | `PTree.Examples.UnifiedRealBernoulliMathCompCore` | `PTree.CaseStudies.BernoulliFactory.UnifiedRealBernoulliMathCompCore` |
| `PTree.CaseStudies.BernoulliFactory.OperationalVonNeumann` | `PTree.Examples.VonNeumannUnbounded` | `PTree.CaseStudies.BernoulliFactory.VonNeumannUnbounded` |
| `PTree.CaseStudies.BernoulliFactory.RealBernoulliMathComp` | `PTree.Examples.RealBernoulliOracle` | `PTree.CaseStudies.BernoulliFactory.RealBernoulliOracle` |
| `PTree.CaseStudies.BernoulliFactory.UnifiedRealBernoulliMathCompCore` | `PTree.Examples.RealBernoulliMathComp` | `PTree.CaseStudies.BernoulliFactory.RealBernoulliMathComp` |
| `PTree.CaseStudies.BernoulliFactory.UnifiedRealBernoulliMathCompCore` | `PTree.Examples.RealBernoulliOracle` | `PTree.CaseStudies.BernoulliFactory.RealBernoulliOracle` |
| `PTree.CaseStudies.InteractiveVonNeumann.InteractiveVonNeumannService` | `PTree.Examples.OperationalVonNeumann` | `PTree.CaseStudies.BernoulliFactory.OperationalVonNeumann` |
| `PTree.CaseStudies.InteractiveVonNeumann.InteractiveVonNeumannService` | `PTree.Examples.VonNeumannUnbounded` | `PTree.CaseStudies.BernoulliFactory.VonNeumannUnbounded` |
| `PTree.Regression.Backend.FreeOmegaEscapingMass` | `PTree.Examples.EnumMeasureRegression` | `PTree.Regression.Backend.EnumMeasureRegression` |
| `PTree.Regression.Backend.FreeOmegaEscapingMass` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Backend.FreeOmegaLimitSafety` | `PTree.Examples.RandomWalk` | `PTree.CaseStudies.RandomWalk` |
| `PTree.Regression.Backend.FreeOmegaUpperContinuity` | `PTree.Examples.FreeOmegaEscapingMass` | `PTree.Regression.Backend.FreeOmegaEscapingMass` |
| `PTree.Regression.Backend.FreeOmegaUpperExpectation` | `PTree.Examples.FreeOmegaEscapingMass` | `PTree.Regression.Backend.FreeOmegaEscapingMass` |
| `PTree.Regression.Backend.FreeOmegaUpperExpectation` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Backend.FreeOmegaUpperObservation` | `PTree.Examples.FreeOmegaEscapingMass` | `PTree.Regression.Backend.FreeOmegaEscapingMass` |
| `PTree.Regression.Backend.FreeOmegaUpperObservation` | `PTree.Examples.FreeOmegaUpperExpectation` | `PTree.Regression.Backend.FreeOmegaUpperExpectation` |
| `PTree.Regression.Backend.FreeOmegaUpperObservation` | `PTree.Examples.RandomWalk` | `PTree.CaseStudies.RandomWalk` |
| `PTree.Regression.Backend.FreeOmegaUpperQuotient` | `PTree.Examples.FreeOmegaEscapingMass` | `PTree.Regression.Backend.FreeOmegaEscapingMass` |
| `PTree.Regression.Backend.FreeOmegaUpperQuotient` | `PTree.Examples.FreeOmegaUpperExpectation` | `PTree.Regression.Backend.FreeOmegaUpperExpectation` |
| `PTree.Regression.Backend.FreeOmegaUpperQuotient` | `PTree.Examples.FreeOmegaUpperObservation` | `PTree.Regression.Backend.FreeOmegaUpperObservation` |
| `PTree.Regression.Backend.FreeOmegaUpperQuotient` | `PTree.Examples.RandomWalk` | `PTree.CaseStudies.RandomWalk` |
| `PTree.Regression.Backend.FreeOmegaUpperQuotient` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Backend.SubEnumRegression` | `PTree.Examples.EnumMeasureRegression` | `PTree.Regression.Backend.EnumMeasureRegression` |
| `PTree.Regression.Backend.UnifiedFrontierEnum` | `PTree.Examples.EnumMeasureRegression` | `PTree.Regression.Backend.EnumMeasureRegression` |
| `PTree.Regression.Infrastructure.CorrelatedInternalRounds` | `PTree.Examples.PairedFiniteCompression` | `PTree.Regression.Infrastructure.PairedFiniteCompression` |
| `PTree.Regression.Infrastructure.CorrelatedInternalRounds` | `PTree.Examples.ResidualFinite` | `PTree.Regression.Infrastructure.ResidualFinite` |
| `PTree.Regression.Infrastructure.CostedRounds` | `PTree.Examples.FiniteInternalPlan` | `PTree.Regression.Infrastructure.FiniteInternalPlan` |
| `PTree.Regression.Infrastructure.CouplingReferences` | `PTree.Examples.CorrelatedSampleAlgebra` | `PTree.Regression.Probability.CorrelatedSampleAlgebra` |
| `PTree.Regression.Infrastructure.CouplingReferences` | `PTree.Examples.EnumMeasureRegression` | `PTree.Regression.Backend.EnumMeasureRegression` |
| `PTree.Regression.Infrastructure.CouplingReferences` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Infrastructure.FiniteInternalRound` | `PTree.Examples.FiniteInternalPlan` | `PTree.Regression.Infrastructure.FiniteInternalPlan` |
| `PTree.Regression.Infrastructure.HiddenRandomState` | `PTree.Examples.CouplingReferences` | `PTree.Regression.Infrastructure.CouplingReferences` |
| `PTree.Regression.Infrastructure.HiddenRandomState` | `PTree.Examples.EnumMeasureRegression` | `PTree.Regression.Backend.EnumMeasureRegression` |
| `PTree.Regression.Infrastructure.HiddenRandomState` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Infrastructure.KernelCongruence` | `PTree.Examples.PEuttAlgebra` | `PTree.Regression.Semantics.PEuttAlgebra` |
| `PTree.Regression.Infrastructure.NativeRecovery` | `PTree.Examples.CouplingReferences` | `PTree.Regression.Infrastructure.CouplingReferences` |
| `PTree.Regression.Infrastructure.NativeRecovery` | `PTree.Examples.FiniteInternalPlan` | `PTree.Regression.Infrastructure.FiniteInternalPlan` |
| `PTree.Regression.Infrastructure.NativeRecovery` | `PTree.Examples.HiddenRandomState` | `PTree.Regression.Infrastructure.HiddenRandomState` |
| `PTree.Regression.Infrastructure.NativeRecovery` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Infrastructure.PairedFiniteCompression` | `PTree.Examples.RandomWalk` | `PTree.CaseStudies.RandomWalk` |
| `PTree.Regression.Infrastructure.ResidualFinite` | `PTree.Examples.RandomWalk` | `PTree.CaseStudies.RandomWalk` |
| `PTree.Regression.Infrastructure.ResidualJointCoinduction` | `PTree.Examples.CouplingReferences` | `PTree.Regression.Infrastructure.CouplingReferences` |
| `PTree.Regression.Infrastructure.ResidualJointCoinduction` | `PTree.Examples.HiddenRandomState` | `PTree.Regression.Infrastructure.HiddenRandomState` |
| `PTree.Regression.Infrastructure.ResidualJointCoinduction` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Infrastructure.ResidualTransport` | `PTree.Examples.ResidualFinite` | `PTree.Regression.Infrastructure.ResidualFinite` |
| `PTree.Regression.Probability.ConditionalResampling` | `PTree.Examples.EnumDisintegration` | `PTree.Regression.Probability.EnumDisintegration` |
| `PTree.Regression.Probability.ConditionalResampling` | `PTree.Examples.EnumMeasureRegression` | `PTree.Regression.Backend.EnumMeasureRegression` |
| `PTree.Regression.Probability.ConditionalResampling` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Probability.CorrelatedSampleAlgebra` | `PTree.Examples.EnumMeasureRegression` | `PTree.Regression.Backend.EnumMeasureRegression` |
| `PTree.Regression.Probability.CorrelatedSampleAlgebra` | `PTree.Examples.PEuttAlgebra` | `PTree.Regression.Semantics.PEuttAlgebra` |
| `PTree.Regression.Probability.CorrelatedSampleAlgebra` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Probability.EnumDisintegration` | `PTree.Examples.EnumMeasureRegression` | `PTree.Regression.Backend.EnumMeasureRegression` |
| `PTree.Regression.Probability.EnumDisintegration` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Semantics.CanonicalPartialDivergence` | `PTree.Examples.EnumMeasureRegression` | `PTree.Regression.Backend.EnumMeasureRegression` |
| `PTree.Regression.Semantics.LabelledMDP` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Semantics.MDPCoincidence` | `PTree.Examples.MDPFragment` | `PTree.Regression.Semantics.MDPFragment` |
| `PTree.Regression.Semantics.MDPCoincidence` | `PTree.Examples.TreeTransitionStrictness` | `PTree.Regression.Semantics.TreeTransitionStrictness` |
| `PTree.Regression.Semantics.MDPEmbedding` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Semantics.MDPFragment` | `PTree.Examples.CorrelatedSampleAlgebra` | `PTree.Regression.Probability.CorrelatedSampleAlgebra` |
| `PTree.Regression.Semantics.MDPFragment` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Semantics.OperationalPTSExamples` | `PTree.Examples.EnumMeasureRegression` | `PTree.Regression.Backend.EnumMeasureRegression` |
| `PTree.Regression.Semantics.PEuttAlgebra` | `PTree.Examples.EnumMeasureRegression` | `PTree.Regression.Backend.EnumMeasureRegression` |
| `PTree.Regression.Semantics.TreeTransition` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
| `PTree.Regression.Semantics.TreeTransitionBisim` | `PTree.Examples.TreeTransition` | `PTree.Regression.Semantics.TreeTransition` |
| `PTree.Regression.Semantics.TreeTransitionSoundness` | `PTree.Examples.InteractiveVonNeumannService` | `PTree.CaseStudies.InteractiveVonNeumann.InteractiveVonNeumannService` |
| `PTree.Regression.Semantics.TreeTransitionSoundness` | `PTree.Examples.TreeTransition` | `PTree.Regression.Semantics.TreeTransition` |
| `PTree.Regression.Semantics.TreeTransitionStrictness` | `PTree.Examples.CorrelatedSampleAlgebra` | `PTree.Regression.Probability.CorrelatedSampleAlgebra` |
| `PTree.Regression.Semantics.TreeTransitionStrictness` | `PTree.Examples.EnumMeasureRegression` | `PTree.Regression.Backend.EnumMeasureRegression` |
| `PTree.Regression.Semantics.TreeTransitionStrictness` | `PTree.Examples.SubEnumRegression` | `PTree.Regression.Backend.SubEnumRegression` |
