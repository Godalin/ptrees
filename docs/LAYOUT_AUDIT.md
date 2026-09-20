# Structural layout audit

This is a repository-local dependency audit, not a theorem-usage or external-client census. It preserves every Coq declaration and proof from the accepted theory baseline.

Regenerate with `python3 tools/audit_layout.py` after a full `opam exec -- dune build`. The script is read-only and fails on any proof-text change outside the namespace transformation.

## Scope and invariance

- Baseline: `92e0841`; 190 Coq modules before and after; 65 moves; zero theorem/module deletions.
- All definition, theorem-statement and proof text is identical after normalizing Require paths; the only other Coq edit updates one comment's regression path.
- All nine `Semantics/` modules and all finite-internal/kernel implementations remain in place.
- [Complete file move manifest](module-moves.tsv): each row also determines the old/new qualified module name; file basenames and declaration names are unchanged. No compatibility wrapper modules were added.
- Classification: 15 files in four case-study groups; 50 regressions (17 semantics, 14 backend, 4 probability, 15 infrastructure). Factory contains ordinary Von Neumann support shared by the interactive service.
- No final MDP-encoding transition corollary or new semantic theorem is part of this milestone.

## Dependency method and retained roots

Coq's `.PTree.theory.d` supplies 1574 direct local Require edges covering all 190 maintained modules. External libraries are excluded. Transitive clients include re-export paths; an import does not prove use of each declaration.

Checked layer boundaries: Core/Prob/Eq/Semantics import no case study or regression; case studies import no regression. Regression-to-case-study reuse is allowed.

Roots are every Core module, every semantic comparison module, the curated facade, the structural/strong and FreeOmega equational endpoints, both concrete trace probability endpoints, and all four retained case-study groups. This deliberately does not treat every regression as a public root.

`PTree.CaseStudies.BernoulliFactory.BernoulliFactory`, `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryComposition`, `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryProbability`, `PTree.CaseStudies.BernoulliFactory.OperationalBernoulliFactory`, `PTree.CaseStudies.BernoulliFactory.OperationalRationalBernoulli`, `PTree.CaseStudies.BernoulliFactory.OperationalRealBernoulliMathComp`, `PTree.CaseStudies.BernoulliFactory.OperationalVonNeumann`, `PTree.CaseStudies.BernoulliFactory.RationalBernoulli`, `PTree.CaseStudies.BernoulliFactory.RealBernoulliMathComp`, `PTree.CaseStudies.BernoulliFactory.RealBernoulliOracle`, `PTree.CaseStudies.BernoulliFactory.UnifiedRealBernoulliMathCompCore`, `PTree.CaseStudies.BernoulliFactory.VonNeumannUnbounded`, `PTree.CaseStudies.InteractiveVonNeumann.InteractiveVonNeumannService`, `PTree.CaseStudies.MixedHeadProtocol`, `PTree.CaseStudies.RandomWalk`, `PTree.Core.PTreeDefinition`, `PTree.Core.PTreeEnum`, `PTree.Core.PTreeProbability`, `PTree.Core.PTreeSubEnum`, `PTree.Core.Utils`, `PTree.Eq.FreeOmega`, `PTree.Eq.PStrong`, `PTree.Eq.PStruct`, `PTree.Eq.ProbabilisticSemantics`, `PTree.Eq.ProbabilisticTraceEnum`, `PTree.Eq.ProbabilisticTraceSubEnum`, `PTree.Semantics.HeadTransition`, `PTree.Semantics.MDPCoincidence`, `PTree.Semantics.MDPCoincidenceFreeOmega`, `PTree.Semantics.MDPEmbedding`, `PTree.Semantics.MDPEmbeddingSubEnum`, `PTree.Semantics.MDPFragment`, `PTree.Semantics.TreeTransition`, `PTree.Semantics.TreeTransitionBisim`, `PTree.Semantics.TreeTransitionSoundness`

Root closure reaches 93 modules; 97 lie outside it. Unreachable modules can still be meaningful regressions or independent measure theorems. All remain built by Dune; no deletion follows from this classification.

### Outside the selected root closure

- `PTree.Eq.FiniteInternal` (24 direct local clients)
- `PTree.Eq.FiniteInternalHitting` (3 direct local clients)
- `PTree.Eq.FiniteInternalJoint` (1 direct local clients)
- `PTree.Eq.FiniteInternalPlan` (14 direct local clients)
- `PTree.Eq.FreeOmega.CostedKernel` (4 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternal` (4 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalAcceleration` (4 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction` (2 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalCostedProjection` (4 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalJoint` (13 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration` (2 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction` (1 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalJointCoverage` (3 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalJointHitting` (3 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalJointReference` (2 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalJointRows` (1 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalJointTruncation` (1 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalNative` (12 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalNativeJoint` (2 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalPlanHitting` (2 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy` (1 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalRound` (6 direct local clients)
- `PTree.Eq.FreeOmega.FiniteInternalRoundCoupling` (4 direct local clients)
- `PTree.Eq.FreeOmega.KernelCompletion` (11 direct local clients)
- `PTree.Eq.FreeOmega.KernelCongruence` (4 direct local clients)
- `PTree.Eq.FreeOmega.KernelContinuity` (4 direct local clients)
- `PTree.Eq.FreeOmega.KernelDisintegration` (1 direct local clients)
- `PTree.Eq.FreeOmega.KernelProjection` (2 direct local clients)
- `PTree.Experimental.UniverseSeparatedPTree` (0 direct local clients)
- `PTree.Prob.Discrete` (0 direct local clients)
- `PTree.Prob.EnumCofinality` (0 direct local clients)
- `PTree.Prob.FinSupp` (0 direct local clients)
- `PTree.Prob.FreeOmegaCodedJointSubEnum` (1 direct local clients)
- `PTree.Prob.FreeOmegaCouplingEnum` (3 direct local clients)
- `PTree.Prob.FreeOmegaEquivalenceJointSubEnum` (1 direct local clients)
- `PTree.Prob.FreeOmegaJointExtension` (2 direct local clients)
- `PTree.Prob.FreeOmegaMeasureEnumAudit` (0 direct local clients)
- `PTree.Prob.FreeOmegaNativeTransportEnum` (0 direct local clients)
- `PTree.Prob.FreeOmegaUpperContinuityEnum` (3 direct local clients)
- `PTree.Prob.FreeOmegaUpperCouplingEnum` (5 direct local clients)
- `PTree.Prob.FreeOmegaUpperExpectationEnum` (7 direct local clients)
- `PTree.Prob.FreeOmegaUpperObservationEnum` (2 direct local clients)
- `PTree.Prob.FreeOmegaUpperQuotientEnum` (1 direct local clients)
- `PTree.Prob.FreeOmegaUpperRelationalEnum` (2 direct local clients)
- `PTree.Prob.MonadList` (0 direct local clients)
- `PTree.Prob.RealSubTypes` (1 direct local clients)
- `PTree.Prob.SemanticCouplingMathComp` (1 direct local clients)
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
- `PTree.Regression.Backend.SubEnumRegression` (15 direct local clients)
- `PTree.Regression.Backend.UnifiedFrontierEnum` (0 direct local clients)
- `PTree.Regression.Backend.UnifiedMathCompFrontier` (0 direct local clients)
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
- `PTree.Regression.Probability.ConditionalResampling` (0 direct local clients)
- `PTree.Regression.Probability.CorrelatedSampleAlgebra` (3 direct local clients)
- `PTree.Regression.Probability.EnumDisintegration` (1 direct local clients)
- `PTree.Regression.Probability.FiniteTransport` (0 direct local clients)
- `PTree.Regression.Semantics.CanonicalPartialDivergence` (0 direct local clients)
- `PTree.Regression.Semantics.HeadTransition` (0 direct local clients)
- `PTree.Regression.Semantics.HittingDivergence` (0 direct local clients)
- `PTree.Regression.Semantics.LabelledMDP` (0 direct local clients)
- `PTree.Regression.Semantics.MDPCoincidence` (0 direct local clients)
- `PTree.Regression.Semantics.MDPEmbedding` (0 direct local clients)
- `PTree.Regression.Semantics.MDPFragment` (1 direct local clients)
- `PTree.Regression.Semantics.OperationalPTSExamples` (0 direct local clients)
- `PTree.Regression.Semantics.PEuttAlgebra` (2 direct local clients)
- `PTree.Regression.Semantics.PEuttNotation` (0 direct local clients)
- `PTree.Regression.Semantics.ProbabilisticRelationHierarchy` (0 direct local clients)
- `PTree.Regression.Semantics.PublicSemanticFacade` (0 direct local clients)
- `PTree.Regression.Semantics.StableHittingComputation` (0 direct local clients)
- `PTree.Regression.Semantics.TreeTransition` (2 direct local clients)
- `PTree.Regression.Semantics.TreeTransitionBisim` (0 direct local clients)
- `PTree.Regression.Semantics.TreeTransitionSoundness` (0 direct local clients)
- `PTree.Regression.Semantics.TreeTransitionStrictness` (1 direct local clients)

### Zero direct local clients (report only)

47 modules have no direct local client. This includes exported roots and executable/negative regression leaves, not just potential dead code.

- `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryComposition` — retained root
- `PTree.CaseStudies.BernoulliFactory.BernoulliFactoryProbability` — retained root
- `PTree.CaseStudies.BernoulliFactory.OperationalRationalBernoulli` — retained root
- `PTree.CaseStudies.BernoulliFactory.OperationalRealBernoulliMathComp` — retained root
- `PTree.CaseStudies.MixedHeadProtocol` — retained root
- `PTree.Core.PTreeSubEnum` — retained root
- `PTree.Experimental.UniverseSeparatedPTree` — built leaf
- `PTree.Prob.Discrete` — built leaf
- `PTree.Prob.EnumCofinality` — built leaf
- `PTree.Prob.FinSupp` — built leaf
- `PTree.Prob.FreeOmegaMeasureEnumAudit` — built leaf
- `PTree.Prob.FreeOmegaNativeTransportEnum` — built leaf
- `PTree.Prob.MonadList` — built leaf
- `PTree.Regression.Backend.BackendCapabilities` — built leaf
- `PTree.Regression.Backend.CouplingRealization` — built leaf
- `PTree.Regression.Backend.ExtendedEnum` — built leaf
- `PTree.Regression.Backend.FreeOmegaLimitSafety` — built leaf
- `PTree.Regression.Backend.FreeOmegaUpperContinuity` — built leaf
- `PTree.Regression.Backend.FreeOmegaUpperQuotient` — built leaf
- `PTree.Regression.Backend.NativeReflection` — built leaf
- `PTree.Regression.Backend.UnifiedFrontierEnum` — built leaf
- `PTree.Regression.Backend.UnifiedMathCompFrontier` — built leaf
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
- `PTree.Regression.Probability.ConditionalResampling` — built leaf
- `PTree.Regression.Probability.FiniteTransport` — built leaf
- `PTree.Regression.Semantics.CanonicalPartialDivergence` — built leaf
- `PTree.Regression.Semantics.HeadTransition` — built leaf
- `PTree.Regression.Semantics.HittingDivergence` — built leaf
- `PTree.Regression.Semantics.LabelledMDP` — built leaf
- `PTree.Regression.Semantics.MDPCoincidence` — built leaf
- `PTree.Regression.Semantics.MDPEmbedding` — built leaf
- `PTree.Regression.Semantics.OperationalPTSExamples` — built leaf
- `PTree.Regression.Semantics.PEuttNotation` — built leaf
- `PTree.Regression.Semantics.ProbabilisticRelationHierarchy` — built leaf
- `PTree.Regression.Semantics.PublicSemanticFacade` — built leaf
- `PTree.Regression.Semantics.StableHittingComputation` — built leaf
- `PTree.Regression.Semantics.TreeTransitionBisim` — built leaf
- `PTree.Regression.Semantics.TreeTransitionSoundness` — built leaf

## Finite-internal / kernel family: complete local client report

Scope: every `Eq/**/FiniteInternal*.v`, plus FreeOmega KernelCompletion, KernelCongruence, KernelProjection, KernelDisintegration, KernelContinuity and CostedKernel. Incoming/outgoing direct lists and transitive client lists are exhaustive within `theories/`. This family is NOT migrated here. Future migration must update its clients together, not infer dead code from historical names.

### `PTree.Eq.FiniteInternal`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FiniteInternalHitting`, `PTree.Eq.FiniteInternalJoint`, `PTree.Eq.FiniteInternalPlan`, `PTree.Eq.FreeOmega.FiniteInternal`, `PTree.Eq.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.FreeOmega.FiniteInternalNative`, `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.PairedFiniteCompression`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`.
- All transitive clients: `PTree.Eq.FiniteInternalHitting`, `PTree.Eq.FiniteInternalJoint`, `PTree.Eq.FiniteInternalPlan`, `PTree.Eq.FreeOmega.FiniteInternal`, `PTree.Eq.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.FreeOmega.FiniteInternalNative`, `PTree.Eq.FreeOmega.FiniteInternalNativeJoint`, `PTree.Eq.FreeOmega.FiniteInternalPlanHitting`, `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Eq.FreeOmega.FiniteInternalRound`, `PTree.Eq.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.PairedFiniteCompression`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.FiniteInternalHitting`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternal`, `PTree.Eq.PEutt`, `PTree.Eq.PStrong`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FiniteInternalJoint`, `PTree.Eq.FreeOmega.FiniteInternalJointHitting`, `PTree.Regression.Infrastructure.ResidualFinite`.
- All transitive clients: `PTree.Eq.FiniteInternalJoint`, `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.PairedFiniteCompression`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.FiniteInternalJoint`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternal`, `PTree.Eq.FiniteInternalHitting`, `PTree.Eq.PStrong`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.SemanticCoupling`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Regression.Infrastructure.PairedFiniteCompression`.
- All transitive clients: `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.PairedFiniteCompression`.

### `PTree.Eq.FiniteInternalPlan`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternal`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.FreeOmega.FiniteInternalNative`, `PTree.Eq.FreeOmega.FiniteInternalNativeJoint`, `PTree.Eq.FreeOmega.FiniteInternalPlanHitting`, `PTree.Eq.FreeOmega.FiniteInternalRound`, `PTree.Eq.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.NativeRecovery`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.FreeOmega.FiniteInternalNative`, `PTree.Eq.FreeOmega.FiniteInternalNativeJoint`, `PTree.Eq.FreeOmega.FiniteInternalPlanHitting`, `PTree.Eq.FreeOmega.FiniteInternalRound`, `PTree.Eq.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.FreeOmega.CostedKernel`

- In retained-root closure: no.
- Direct imports: `PTree.Eq.FreeOmega.KernelContinuity`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.FreeOmega.FiniteInternal`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternal`, `PTree.Eq.PStrong`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.FreeOmega.FiniteInternalAcceleration`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternal`, `PTree.Eq.FreeOmega.FiniteInternal`, `PTree.Eq.FreeOmega.FiniteInternalJoint`, `PTree.Eq.FreeOmega.KernelContinuity`, `PTree.Eq.PEutt`, `PTree.Eq.PStrong`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaCoupling`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.SemanticCoupling`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`.

### `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternalPlan`, `PTree.Eq.FreeOmega.CostedKernel`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.FreeOmega.FiniteInternalNative`, `PTree.Eq.FreeOmega.FiniteInternalRound`, `PTree.Eq.PEutt`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.FreeOmegaNative`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Infrastructure.CostedRounds`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternalPlan`, `PTree.Eq.FreeOmega.CostedKernel`, `PTree.Eq.FreeOmega.FiniteInternalNative`, `PTree.Eq.FreeOmega.FiniteInternalRound`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.FreeOmegaNative`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.FreeOmega.FiniteInternalJoint`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.PStrong`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaCoupling`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.SemanticCoupling`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.FreeOmega.FiniteInternalNative`, `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.FreeOmega.FiniteInternalNative`, `PTree.Eq.FreeOmega.FiniteInternalNativeJoint`, `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Eq.FreeOmega.FiniteInternalRound`, `PTree.Eq.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternal`, `PTree.Eq.FreeOmega.FiniteInternalJoint`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.FreeOmega.KernelCompletion`, `PTree.Eq.FreeOmega.KernelCongruence`, `PTree.Eq.FreeOmega.KernelContinuity`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.SemanticCoupling`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternal`, `PTree.Eq.FreeOmega.FiniteInternalJoint`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.PEutt`, `PTree.Eq.PStrong`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.SemanticCoupling`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Regression.Infrastructure.CorrelatedInternalRounds`.
- All transitive clients: `PTree.Regression.Infrastructure.CorrelatedInternalRounds`.

### `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternal`, `PTree.Eq.FreeOmega.FiniteInternal`, `PTree.Eq.FreeOmega.FiniteInternalJoint`, `PTree.Eq.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.FreeOmega.KernelCompletion`, `PTree.Eq.FreeOmega.KernelCongruence`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.FreeOmega.FiniteInternalJointHitting`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternal`, `PTree.Eq.FiniteInternalHitting`, `PTree.Eq.FreeOmega.FiniteInternalJoint`, `PTree.Eq.FreeOmega.KernelCompletion`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.FreeOmega.FiniteInternalJointReference`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternal`, `PTree.Eq.FreeOmega.FiniteInternalJoint`, `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.PEutt`, `PTree.Eq.PStrong`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaCoupling`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.SemanticCoupling`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.FreeOmega.FiniteInternalJointRows`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternalPlan`, `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.FreeOmega.FiniteInternalNative`, `PTree.Eq.FreeOmega.FiniteInternalRound`, `PTree.Eq.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Eq.PEutt`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.FreeOmegaNative`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Regression.Infrastructure.NativeRecovery`.
- All transitive clients: `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternal`, `PTree.Eq.FreeOmega.FiniteInternal`, `PTree.Eq.FreeOmega.FiniteInternalJoint`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.SemanticCoupling`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.FreeOmega.FiniteInternalNative`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternal`, `PTree.Eq.FiniteInternalPlan`, `PTree.Eq.FreeOmega.FiniteInternalJoint`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.FreeOmegaNative`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.FreeOmega.FiniteInternalNativeJoint`, `PTree.Eq.FreeOmega.FiniteInternalRound`, `PTree.Eq.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.NativeRecovery`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.FreeOmega.FiniteInternalNativeJoint`, `PTree.Eq.FreeOmega.FiniteInternalRound`, `PTree.Eq.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalNative`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.FreeOmega.FiniteInternalNativeJoint`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternalPlan`, `PTree.Eq.FreeOmega.FiniteInternalNative`, `PTree.Eq.FreeOmega.FiniteInternalRoundCoupling`, `PTree.Eq.PStrong`, `PTree.Prob.FreeOmegaJointExtension`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.FreeOmegaNative`, `PTree.Prob.SemanticCoupling`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.NativeRecovery`.
- All transitive clients: `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.FreeOmega.FiniteInternalPlanHitting`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternalPlan`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.FreeOmegaNative`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalRound`, `PTree.Regression.Infrastructure.FiniteInternalPlan`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.FreeOmega.FiniteInternalRound`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalPlan`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternal`, `PTree.Eq.FreeOmega.FiniteInternal`, `PTree.Eq.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJoint`, `PTree.Eq.FreeOmega.KernelCompletion`, `PTree.Eq.FreeOmega.KernelProjection`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Regression.Infrastructure.HiddenRandomState`.
- All transitive clients: `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`.

### `PTree.Eq.FreeOmega.FiniteInternalRound`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternalPlan`, `PTree.Eq.FreeOmega.FiniteInternalNative`, `PTree.Eq.FreeOmega.FiniteInternalPlanHitting`, `PTree.Eq.PTreeKernel`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.FreeOmegaNative`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalRound`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.FiniteInternalRound`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.FreeOmega.FiniteInternalRoundCoupling`

- In retained-root closure: no.
- Direct imports: `PTree.Core.PTreeDefinition`, `PTree.Eq.FiniteInternalPlan`, `PTree.Eq.FreeOmega.FiniteInternalNative`, `PTree.Eq.PStrong`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Eq.UnifiedFrontier`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.FreeOmegaNative`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.FreeOmega.FiniteInternalNativeJoint`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.NativeRecovery`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.FreeOmega.FiniteInternalNativeJoint`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.NativeRecovery`.

### `PTree.Eq.FreeOmega.KernelCompletion`

- In retained-root closure: no.
- Direct imports: `PTree.Eq.PrimitiveStableHitting`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Eq.FreeOmega.KernelCongruence`, `PTree.Eq.FreeOmega.KernelDisintegration`, `PTree.Eq.FreeOmega.KernelProjection`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.KernelCompletion`, `PTree.Regression.Infrastructure.KernelCongruence`, `PTree.Regression.Probability.ConditionalResampling`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.FreeOmega.FiniteInternalJointHitting`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Eq.FreeOmega.KernelCongruence`, `PTree.Eq.FreeOmega.KernelDisintegration`, `PTree.Eq.FreeOmega.KernelProjection`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.KernelCompletion`, `PTree.Regression.Infrastructure.KernelCongruence`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.ConditionalResampling`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.FreeOmega.KernelCongruence`

- In retained-root closure: no.
- Direct imports: `PTree.Eq.FreeOmega.KernelCompletion`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.FreeOmega.KernelDisintegration`, `PTree.Regression.Infrastructure.KernelCongruence`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointCoverage`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.FreeOmega.FiniteInternalJointTruncation`, `PTree.Eq.FreeOmega.KernelDisintegration`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.KernelCongruence`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Probability.ConditionalResampling`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.FreeOmega.KernelContinuity`

- In retained-root closure: no.
- Direct imports: `PTree.Eq.PrimitiveStableHitting`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.CostedKernel`, `PTree.Eq.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Regression.Infrastructure.KernelContinuity`.
- All transitive clients: `PTree.Eq.FreeOmega.CostedKernel`, `PTree.Eq.FreeOmega.FiniteInternalAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalCostedCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalCostedProjection`, `PTree.Eq.FreeOmega.FiniteInternalJointAcceleration`, `PTree.Eq.FreeOmega.FiniteInternalJointCoinduction`, `PTree.Eq.FreeOmega.FiniteInternalJointReference`, `PTree.Eq.FreeOmega.FiniteInternalJointRows`, `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Backend.NativeReflection`, `PTree.Regression.Infrastructure.CorrelatedInternalRounds`, `PTree.Regression.Infrastructure.CostedRounds`, `PTree.Regression.Infrastructure.CouplingReferences`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.KernelContinuity`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualFinite`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`, `PTree.Regression.Infrastructure.ResidualTransport`, `PTree.Regression.Probability.CorrelatedSampleAlgebra`, `PTree.Regression.Semantics.MDPCoincidence`, `PTree.Regression.Semantics.MDPFragment`, `PTree.Regression.Semantics.TreeTransitionStrictness`.

### `PTree.Eq.FreeOmega.KernelDisintegration`

- In retained-root closure: no.
- Direct imports: `PTree.Eq.FreeOmega.KernelCompletion`, `PTree.Eq.FreeOmega.KernelCongruence`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Prob.EnumDisintegration`, `PTree.Prob.FreeOmegaDisintegration`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.TwoLevelMeasure`, `PTree.Prob.TwoLevelMeasureSubEnum`.
- Direct clients: `PTree.Regression.Probability.ConditionalResampling`.
- All transitive clients: `PTree.Regression.Probability.ConditionalResampling`.

### `PTree.Eq.FreeOmega.KernelProjection`

- In retained-root closure: no.
- Direct imports: `PTree.Eq.FreeOmega.KernelCompletion`, `PTree.Eq.PrimitiveStableHitting`, `PTree.Prob.FreeOmegaCoupling`, `PTree.Prob.FreeOmegaMeasure`, `PTree.Prob.TwoLevelMeasure`.
- Direct clients: `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.HiddenRandomState`.
- All transitive clients: `PTree.Eq.FreeOmega.FiniteInternalProjectedPolicy`, `PTree.Regression.Infrastructure.HiddenRandomState`, `PTree.Regression.Infrastructure.NativeRecovery`, `PTree.Regression.Infrastructure.ResidualJointCoinduction`.

## All changed Require paths

83 imported-module occurrences in 43 client files change namespace.

Each row is one imported module occurrence (source now uses the new namespace). Multi-module statements were split only when their destinations differ, preserving import order.

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
