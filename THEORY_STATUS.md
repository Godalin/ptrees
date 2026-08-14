# Maintained probabilistic equivalence theory

This file maps the maintained theory to its checked Coq artifacts.  Unless a
condition is listed explicitly, the referenced result is proved without an
`Admitted` axiom in the default installed theory.

## Two-level unified-frontier migration

- `Prob/TwoLevelMeasure.v` introduces the universe-polymorphic model now used
  for the next API: node measures `MN` and semantic/frontier measures `MF`
  are independent, connected only by an explicit mixed bind and its
  extensional/coupling laws.  Omega order and continuity are capabilities of
  `MF`, not assumptions built into PTree syntax.
- `Eq/UnifiedFrontier.v` defines one public `frontier` judgment.  Finite
  `Ret`/`Vis`/`Tau`/`Prob` derivations are native rules rather than an
  `AUFFinite` wrapper; AST iteration uses `MN`-to-`MF` finite approximants and
  an `MF` omega limit.
- `Prob/TwoLevelMeasureEnum.v` is the first concrete model, with
  `MN = MF = Enum`.  `Examples/UnifiedFrontierEnum.v` checks the new semantics
  on the existing split-mass regression.  `Eq/UnifiedFrontierEnumFacts.v`
  proves a bidirectional correspondence between the AST-aware `aufrontier`
  and the single new judgment (with mutually inverse head pushforwards), and
  embeds finite `apfrontier` derivations as a compatibility layer.  In
  particular, a unified iteration whose step proof is already unbounded maps
  back to the old `AUFNestedIter`; the finite/unbounded distinction is not
  present in the public judgment.  The file also proves that mixed finite
  iteration is exactly the old
  `meas_iter_approx/meas_iter` on Enum.  The established hierarchy below
  remains the maintained compatibility baseline while equivalence, PTS and
  examples are migrated incrementally.
- `Eq/UnifiedPWeak.v` defines the new backend-independent `weak_bisim`
  directly over the single frontier and split `MN`/`MF` couplings.  It is a
  coinductive greatest fixed point with guarded Tau/Prob rules; fold/unfold,
  result-relation monotonicity, reflexivity, symmetry, and the common-frontier
  introduction theorem are checked without referring to the legacy weak
  relations.  Transitivity is intentionally pending the explicit unified
  frontier-coherence package rather than being assumed.
- `Eq/UnifiedPWeakEnumFacts.v` proves that every established Enum `auweak`
  derivation maps to the new `weak_bisim`, translating both directions of
  frontier matching and pushing old head couplings through the representation
  isomorphism.  `Examples/UnifiedPWeakEnumExamples.v` applies that theorem to
  the unbounded Von Neumann sampler versus a terminating fair coin and to the
  closed `p = 1/3` to `q = 2/5` Bernoulli factory versus a direct terminating
  `q`-coin.
- `Eq/UnifiedProbabilisticPTS.v` gives an independent distribution-valued
  transition presentation for the two-level model: primitive residual
  transitions live in `MN`, stable weak distributions live in `MF`, and
  `mixed_bind` connects them.  It proves `unified_ppts_weak <-> frontier` and,
  for the divergence-sensitive guarded PTS, the full characterization
  `weak_bisim <-> unified_ppts_bisim`.

## Measure semantics and coupling

- `Prob/FrontierLift.v` defines the backend-independent `MeasureInterface`.
  Its `meas_eq` is semantic equality; concrete representation equality is not
  part of the interface.
- `Prob/FrontierLiftEnum.v` implements extensional Enum equality with indexed
  couplings.  `enum_repr_eq` separately names literal list equality.
- `MeasureLaws`, `MeasureBindLaws`, `MeasureLiftBindLaws`,
  `MeasureLiftAELaws`, `MeasureCongruenceLaws`, and `MeasureMonadLaws` expose
  the exact algebraic assumptions used by later proofs.
- Enum proves the required coupling composition and Kleisli laws.  The
  reordering, duplicate/split-mass, Dirac, and nested-flattening checks are in
  `Examples/EnumMeasureRegression.v`.

## Finite and AST frontiers

- `Eq/PWeakAbstract.v`: `apfrontier_deterministic` and
  `apfrontier_sem_unique` give finite uniqueness up to `meas_eq`;
  `apfrontier_sem_prob_ret` and `apfrontier_sem_prob_flatten` provide the
  principal Dirac and flattening rules.
- `Prob/MeasureIteration.v` defines finite approximants, omega limits,
  totality, and AST certificates.
- `Eq/PWeakUnbounded.v` defines `aufrontier`, including finite, Tau, Prob,
  iteration, bind, and nested-iteration closure.  Omega/frontier uniqueness is
  stated explicitly by `UnboundedFrontierCoherence` rather than hidden in a
  backend instance.

## Weak equivalence and composition

- `Eq/PWeakAbstractTrans.v` proves raw finite `apweak` transitivity.
- `Eq/PWeakUnboundedTrans.v` proves `auweak_trans` and installs
  `auweak_equivalence`; raw `auweak`, not `auequiv`, is the maintained
  AST-aware weak probabilistic bisimilarity.
- `Examples/PWeakFrontierExamples.v` contains the concrete divergence
  counterexample `unrestricted_bind_congruence_fails`.
- `Eq/PWeakUnbounded.v` proves the positive, explicitly conditioned rules
  `auweak_bind_common_frontier` and `auweak_bind_common_frontier_sem`.

## Distribution-valued PTS characterization

- `Eq/ProbabilisticPTS.v` defines distribution-valued finite and AST weak
  transitions.
- `ppts_weak_iff_apfrontier` and `ppts_ast_weak_iff_aufrontier` prove the two
  frontier correspondences.
- `auweak_ppts_bisim_sound` proves soundness for the ordinary weak-only PTS
  bisimulation.  `ppts_bisim_complete_productive` proves completeness under
  its stated productivity condition.
- `ppts_guarded_iff_auweak` is an unconditional two-way characterization for
  the divergence-sensitive guarded PTS semantics.

## Relation hierarchy

- `Eq/PStrong.v` defines the axiom-free coinductive `pstructural` relation:
  Ret/Tau/Vis are lockstep and Prob requires the same measure with pointwise
  related continuations.  `pstructural_equivalence` proves it is an
  equivalence, `pstructural_pstrong` proves its inclusion in `pstrong`, and
  `eq_pstructural` embeds tree identity.
- `Eq/PWeakHierarchy.v`: `pstrong_apweak` proves strong-to-finite weak
  inclusion from the measure laws; `apweak_auweak_of_finite_generation` and
  `pstrong_auweak_of_finite_generation` state the exact finite-generation
  condition needed to enter the AST-aware relation.

## Checked examples and observable consequences

- `Examples/VonNeumannUnbounded.v` proves the unbounded biased-coin extractor
  AST and `auweak`-equivalent to a direct fair toss.
- `Examples/BernoulliFactory.v` proves that any normalized nontrivial rational
  source coin can drive two AST loops to implement a rational target coin;
  `third_coin_simulates_two_fifths_correct` is the closed `1/3 -> 2/5`
  instance.
- `Examples/RealBernoulliOracle.v` proves the oracle sampler's finite-prefix
  law and a uniform geometric vanishing bound for its missing mass.
  `Examples/RealBernoulliMathComp.v` then proves
  `mathcomp_binary_oracle_lub`: whenever those prefixes represent a real
  parameter `q`, the unbounded result measure is the genuine MathComp
  Bernoulli `q`; `mathcomp_binary_oracle_is_ast` proves AST.  This is the
  maintained real-valued behavioral result semantics.  It is deliberately
  not advertised as `auweak`, whose recursive-frontier universe is outside
  the current MathComp/HB support boundary documented below.
- `Eq/PWeakObservableEnum.v` proves Boolean return-event preservation from
  Enum couplings.  The Von Neumann and Bernoulli factory files instantiate it
  for the probability of returning `true`.

## MathComp Analysis boundary

- `Prob/MathCompMeasure.v` provides the measure, bind, subprobability, omega,
  and AST backend.  `MathCompCouplingGluing` is an explicit assumption because
  gluing is not a theorem of the bare measure interface on arbitrary types.
- The current PTree measure constructor is monomorphic.  Embedding MathComp's
  higher-universe measurable kernels into `auweak` therefore requires a
  systematic universe-polymorphism refactor.  The experimental MathComp PTree
  clients are excluded from the default installed theory; the checked Enum
  cases provide the current end-to-end program equivalences.
- `Experimental/UniverseSeparatedPTree.v` is a checked migration probe.  It
  separates `M`'s sampled-carrier and measure-representation universes and
  successfully constructs a PTree probability node from
  `MathCompKernelMeasure` and a real Bernoulli kernel.  This confirms the
  required node-level signature change.  The same file now records two
  further compile-time boundaries: the same fixed `M` cannot measure a
  frontier head containing its recursive tree, while an abstract two-level
  `(MN, MF)` signature can.  `TwoLevelMeasureInterface` isolates the mixed
  operation required by the probabilistic frontier rule: integrating an
  `MF`-valued frontier kernel against an `MN` node measure.  Finally, a
  checked negative probe shows that the current monomorphic-universe
  `MathCompKernelMeasure` cannot be instantiated independently as both `MN`
  and `MF`.  A polymorphic kernel type synonym does make the abstract
  two-level shape typecheck, and the sealed bind has the desired mixed type
  at its original levels.  A final negative regression shows why that is not
  yet enough: HB kernel operations and measurable instances already sealed
  below the recursive frontier cannot construct its measure.  The probe also
  asks HB to generate a new measurable carrier at an explicitly selected
  higher universe; MathComp's hierarchy constrains it back below the same
  global bound, so that local workaround is rejected as well.  End-to-end
  MathComp `auweak` therefore needs a genuinely universe-polymorphic
  MathComp/HB hierarchy (likely an upstream change), or a non-HB frontier
  backend with the required mixed bind, coupling, and omega laws.  This is an
  explicit backend boundary, not an assumed real-valued program equivalence.

## Deliberately deferred

- A new probabilistic refinement/simulation replacing legacy `PSSim`.
- Bidirectional ITree compilation bridges.
- Compatibility with every auxiliary rule of the legacy structural `equ`.
  The maintained hierarchy uses the smaller axiom-free `pstructural` instead.

The default validation command is:

```text
dune build -p coq-ptree @install
```
