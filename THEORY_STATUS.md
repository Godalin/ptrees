# Maintained probabilistic equivalence theory

This file maps the maintained theory to its checked Coq artifacts.  Unless a
condition is listed explicitly, the referenced result is proved without an
`Admitted` axiom in the default installed theory.

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
