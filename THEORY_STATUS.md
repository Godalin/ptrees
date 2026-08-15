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
  Enum also proves the diagonal-AE coupling capability directly from its
  nonzero-support semantics, so it and MathComp satisfy the same optional AE
  Kleisli interface rather than relying on backend-specific shortcuts.
- `Eq/UnifiedPWeak.v` defines the new backend-independent `weak_bisim`
  directly over the single frontier and split `MN`/`MF` couplings.  It is a
  coinductive greatest fixed point with guarded Tau/Prob rules; fold/unfold,
  result-relation monotonicity, reflexivity, symmetry, and the common-frontier
  introduction theorem are checked without referring to the legacy weak
  relations.  `UnifiedFrontierCoherence` makes the two additional conditions
  needed by transitivity explicit: extensional frontier uniqueness and Tau
  inversion.  `Eq/UnifiedPWeakTrans.v` proves relational composition and
  transitivity under exactly that package, using `MF` gluing for frontier
  couplings and `MN` gluing for primitive probabilistic residuals; consequently
  `weak_bisim eq` is an `Equivalence` whenever coherence is available.
- `Eq/UnifiedPWeakEnumFacts.v` proves that every established Enum `auweak`
  derivation maps to the new `weak_bisim`, translating both directions of
  frontier matching and pushing old head couplings through the representation
  isomorphism.  `Examples/UnifiedPWeakEnumExamples.v` applies that theorem to
  the unbounded Von Neumann sampler versus a terminating fair coin and to the
  closed `p = 1/3` to `q = 2/5` Bernoulli factory versus a direct terminating
  `q`-coin.
  A legacy Enum `UnboundedFrontierCoherence` witness transports to the new
  coherence package through the bidirectional head isomorphism.
- `Examples/UnifiedPWeakEnumExamples.v` also contains a direct finite proof,
  not routed through a legacy relation: a two-level nested sampler with split
  mass is unified-weak-bisimilar to one terminating three-point sample.  The
  proof combines native unified frontiers, Kleisli associativity, Enum
  extensional equality, and coupling properness.
- `Eq/UnifiedProbabilisticPTS.v` gives a distribution-valued operational
  presentation of the two-level frontier.  Its current weak rules mirror the
  frontier's Iter/Bind/NestedIter rules, so the proved equivalences
  `unified_ppts_weak <-> frontier` and
  `weak_bisim <-> unified_ppts_bisim` are representation/transport results,
  not yet an independent standard-model validation.
  The finite nested sampler, Von Neumann extractor, rational Bernoulli
  factory, and real MathComp oracle examples each instantiate the forward
  direction as a checked concrete PTS-bisimulation corollary.
- `Eq/OperationalProbabilisticPTS.v` starts the independent replacement.  It
  defines one universe-safe primitive kernel into `MF`, a generic fuel-bounded
  stable-hitting distribution obtained only by repeatedly binding that
  kernel, a subprobability weak behavior as its omega limit, and AST as the
  separate assertion that this limit is total.
  There are no Iter/Bind/NestedIter weak constructors.  The development also
  identifies and proves for Enum and FreeOmega the previously implicit mixed
  associativity law needed to derive the operational Prob recurrence.  A
  separate minimal order capability (reflexivity, bottom zero, and bind
  monotonicity) proves that every primitive hitting chain is increasing;
  together with omega laws this yields existence and extensional uniqueness
  of its operational weak limit.  The first guarded operational bisimulation
  is now defined as a greatest fixed point: cross-shape matching requires
  total operational AST limits, while Ret/Vis/Tau/Prob and one-sided Tau
  remain guarded rules.  Consequently the zero hitting limit of pure
  divergence cannot by itself justify an arbitrary equivalence.  Fold/unfold,
  monotonicity, reflexivity, and common-AST introduction are checked.
  As a prerequisite for those soundness laws, omega limits are now congruent
  under pointwise semantic equality of chains (`sem_lub_chain_proper`).
  FreeOmega's lub judgment consequently relates an output to its formal lub
  by semantic equality, rather than requiring literal equality of syntax.
  Both the structural and observation-closed FreeOmega models implement this
  strengthened law; the real-oracle mixed-iteration witness was migrated to
  the observation-closed relation without adding a gluing assumption.
  Finite-prefix invariance is exposed separately as
  `SemanticOmegaCofinalityLaws`: the observation-closed FreeOmega equality
  validates it by quotienting formal lubs by a leading zero approximant.
  `operational_weak_tau_iff` and `operational_ast_weak_tau_iff` then derive
  silent-step invariance solely from the primitive hitting recurrence and
  cofinality; no Tau weak-transition constructor is used.
  `MixedMeasureOmegaLaws` isolates the two further facts required by a
  primitive probability node: sampling an everywhere-zero continuation is
  zero, and mixed bind commutes with almost-everywhere branchwise increasing
  lubs.  The observation-closed FreeOmega model validates both explicitly.
  Consequently `operational_weak_prob` and `operational_ast_weak_prob` prove
  the native Prob soundness rule from primitive fuel recurrence and monotone
  convergence, without importing the frontier's `UFProb` constructor.
  Cofinality also records the constant-chain law, yielding checked
  `operational_weak_ret` and `operational_weak_vis` theorems.  Thus all four
  primitive PTree observations now have sound unbounded hitting laws; the
  remaining frontier soundness gap is specifically compositional Bind and
  the diagonal/cofinal comparison for syntactic iteration.
- `Eq/PrimitiveStableHitting.v` now factors the behavioral core one level
  below PTree.  For an arbitrary primitive kernel `S -> MF (A + S)` (encoded
  by `stable_target`), it defines finite stable-hitting approximants, their
  subprobability omega-limit weak behavior, and AST as totality of that
  limit.  Monotonicity, existence, and extensional uniqueness use only the
  semantic measure order/omega capabilities.  This module contains no PTree,
  frontier, Bind, Iter, or NestedIter reference.  The next refactoring step
  is to prove the current PTree `operational_kernel` is an instance of this
  generic construction and then make the generic definitions the public
  ones.  The first half is now checked: `ptree_primitive_kernel` maps one
  observed PTree state to a distribution of stable heads or next observed
  states, and `ptree_primitive_hitting_adequate` proves pointwise semantic
  equality with the former PTree-specific approximants for every finite
  fuel.  `ptree_primitive_weak_adequate` and
  `ptree_primitive_ast_adequate` lift that result to omega-limit weak behavior
  and AST.  Thus existing examples already have a theorem-level path into
  the generic standard model; changing the public definitions can now be a
  compatibility refactoring rather than a new semantic assumption.
  Representative clients now state this endpoint explicitly rather than
  leaving it implicit in the bridge theorem:
  `operational_reg_nested_primitive_ast` covers the finite nested Enum
  regression, `operational_vn_compiled_primitive_ast` the unbounded
  Von Neumann sampler, `operational_rational_coin_primitive_ast` the
  fair-to-q binary algorithm, and
  `operational_mathcomp_oracle_primitive_ast` the real-oracle MathComp
  backend.  These conclusions all use the same generic `stable_hitting_ast`
  predicate despite their different concrete measure instances and
  productivity proofs.
  The generic layer now also owns the guarded greatest-fixed-point relation
  `stable_kernel_bisim`.  Its stable rule couples independently established
  AST limits, while its primitive-step rule couples stable targets and keeps
  residual states under the coinductive guard.  Hence two states with no AST
  behavior cannot be related vacuously: they must continue to match actual
  kernel transitions.  Stable observations are related by a monotone
  relation transformer `AR sim`, rather than a fixed result relation, so
  observations containing continuations (such as PTree visible heads) can
  refer back to the current candidate bisimulation.  Fold/unfold,
  monotonicity, and reflexivity are checked using `coq-coinduction`; there is
  no Paco-level definition and no syntax-specific Tau/Prob/Iter rule in this
  generic relation.
  Weak stuttering is likewise behavioral: `stable_kernel_silent_l/r` says
  that a kernel is semantically a Dirac transition to one residual state,
  and the two silent rules remove such a step on either side.  They do not
  inspect or mention a PTree Tau constructor.
  `primitive_ptree_bisim` instantiates this generic gfp with
  `ptree_primitive_kernel` and the recursive frontier-head relation; PTree
  syntax occurs only in the adapter kernel.  The rational Bernoulli endpoint
  `primitive_binary_rational_coin_bisim_direct` is the first equivalence
  proved directly in this new public relation.  Its distribution coupling
  is relation-parametric and is shared with the compatibility
  `operational_bisim` proof, rather than transported from that old relation.
  The same direct endpoint has now been checked for all migrated clients:
  `primitive_reg_nested_merged_bisim`,
  `primitive_von_neumann_compiled_direct_bisim`, and
  `primitive_mathcomp_binary_oracle_bisim_direct`.  Their low-level output
  couplings were generalized over the continuation relation, then
  instantiated independently for the compatibility relation and the new
  primitive-kernel gfp.  Thus the generic equivalences do not assume an
  inclusion theorem from the old bisimulation.
  A later behavioral-equivalence audit found that the original coinductive
  one-sided semantic-silent rules were too strong: a Dirac residual
  self-loop could reuse the coinduction hypothesis forever and become
  related to an arbitrary state.  Commit `6acc311` mechanized both absorption
  directions before the rules were removed.  No maintained primitive client
  depended on them.  Any future silent convenience must therefore use an
  inductive finite closure or an explicit progress argument.
  The repaired generic relation has a checked heterogeneous converse theorem
  and observation-transformer monotonicity.  The transitivity audit exposed
  one missing invariant in the original [SKBStep]: a one-step coupling alone
  did not say whether total stable hitting was preserved.  Every generator
  clause now carries `stable_kernel_ast_match`, a bidirectional certificate
  transporting AST limits and their observation coupling.  `SKBAST` clients
  obtain this certificate from omega-limit uniqueness; `SKBStep` must supply
  it as part of being a behavioral, rather than merely local, step match.
  Consequently `stable_kernel_bisim_ast_match` is unconditional, the mixed
  `AST x Step` cases close compositionally, and
  `stable_kernel_bisim_compose` needs only coupling composition plus `AR`
  composition.  The PTree instance now proves reflexivity, symmetry, and
  transitivity and installs `primitive_ptree_bisim_equivalence`.
  `BehavioralDomain` packages the domain assumptions for comparing this
  native relation with the structured proof system: every member has a
  frontier, every such frontier is total, and primitive residual states plus
  visible continuations remain in the domain almost everywhere.  When the
  recursive pairs of `weak_bisim` and `primitive_ptree_bisim` stay in two
  such domains, `weak_bisim_to_primitive_ptree_bisim_on_domain` proves
  soundness by showing that the proof relation itself is a post-fixed point
  of the native generator.  The converse theorem realizes native AST
  coherence through the domains' total frontiers, and
  `weak_bisim_iff_primitive_ptree_bisim_on_domain` gives the resulting
  domain-relative full-abstraction statement.  No unrestricted equivalence
  is claimed for partial/divergent states.
  That gap is now factored precisely. `SemanticMeasureDiagonalLaws` states
  joint omega continuity when both a source distribution and its continuation
  kernels grow along the same diagonal; observation-closed FreeOmega provides
  a checked instance. `operational_bind_diagonal_approx` and
  `operational_bind_cofinal` separate this analytic fact from the PTree-level
  comparison between global primitive fuel and diagonal source/continuation
  fuel, yielding conditional `operational_weak_bind` and AST variants.
  Likewise `operational_iter_round_approx` and `operational_iter_cofinal`
  isolate the comparison between structured iteration rounds and primitive
  steps. Under exactly Bind cofinality and productive iteration cofinality,
  `frontier_to_operational_weak` proves soundness for every unified frontier
  constructor. These premises contain no mirrored weak-transition rules;
  proving them structurally is the remaining adequacy task.
  This conditional soundness now lands in the genuinely independent model:
  `frontier_to_primitive_stable_weak` composes structured-frontier soundness
  with pointwise PTree-kernel adequacy, and
  `frontier_to_primitive_stable_ast` adds totality. Their conclusions mention
  only `stable_hitting_weak/ast` for `ptree_primitive_kernel`; no frontier
  constructor occurs on the semantic side.
  The reverse direction is deliberately domain-relative rather than claimed
  for all syntax. `primitive_frontier_realizable_on Productive` is the exact
  remaining obligation: on the selected productive domain, the structured
  frontier must realize one limit of the independently defined primitive
  hitting chain. `primitive_stable_weak_complete_on` then uses uniqueness of
  that hitting limit to show that every primitive weak result is semantically
  equal to a frontier result. This is not a mirrored transition system or a
  circular completeness assumption: the realizability witness is expected
  to come from structural decomposition, Bind/nested diagonal cofinality,
  and Iter productivity. An unrestricted theorem would be false for the
  intended frontier, because primitive weak hitting assigns the zero
  subdistribution to divergence whereas frontier iteration admits only its
  productive/AST cases.
- `Examples/OperationalPTSExamples.v` is the first direct client of the
  independent model.  A genuinely nested two-sample Enum program and a
  differently shaped one-sample three-point program receive separate
  primitive operational weak limits in `FreeOmega Enum`.  Both limits are
  proved total through low-level observations, and an observation-closed
  coupling derived from the established flattening equality feeds
  `OPBStable` directly.  The resulting
  `operational_reg_nested_merged_bisim` uses neither the mirrored PTS nor a
  transport from unified-frontier bisimulation.
- The intended non-circular proof boundary is now exposed by
  `operational_bisim_of_ast_lift`: the two programs establish AST from their
  own primitive hitting chains (which may have different finite prefixes,
  schedules, and FreeOmega representations), and only their resulting stable
  distributions are coupled.  Requiring literally the same output is merely
  the convenient special case `operational_bisim_of_common_ast`.  In
  particular, the unbounded Von Neumann retry loop and the one-step fair
  sampler do not share an operational design: the former needs a geometric
  productivity/omega argument, while the latter is discharged by the native
  Prob rule.  Their equivalence is nontrivial exactly at the limit-coupling
  boundary, not because matching syntax was built on both sides.
  The older `operational_bisim` generator is retained only as a compatibility
  layer for migrated clients.  It directly mentions Ret/Vis/Tau/Prob shapes
  and is not the semantic relation used by the proof/native full-abstraction
  theorem; the public native equivalence is `primitive_ptree_bisim`.
  `Examples/OperationalBernoulliFactory.v` is now a maintained client of this
  boundary.  It unfolds the actual two-toss source program, proves its raw
  global-fuel hitting chain cofinal with the Von Neumann round schedule, and
  obtains the fair inner sampler as an AST primitive limit.  The outer
  `p -> q` loop is handled by the direct two-dimensional primitive execution
  grid in `OperationalProbabilisticPTSFreeOmega.v`: inner fuel approximates
  each unbounded fair-bit call, outer fuel counts binary-algorithm rounds, and
  diagonal cofinality plus the FreeOmega Fubini law relates this grid to the
  program's single global primitive-fuel chain.  No Iter/Bind/NestedIter weak
  constructor or `pstructural` normalization occurs in this proof.
  Each actual unbounded binary step is observation-coupled to the standard
  finite `binary_coin_transition`.  These step couplings compose through the
  outer rows, so the implementation's weak result can be chosen to be the
  standard rational-Bernoulli limit.  The latter supplies totality, yielding
  `operational_biased_to_rational_coin_ast` and the direct generic endpoint
  `primitive_biased_to_rational_coin_bisim_direct`.  The closed theorem
  `primitive_third_to_two_fifths_bisim_direct` relates the genuinely
  unbounded `1/3 -> 2/5` factory to the one-step terminating `2/5` sampler.
  The obsolete pair-program, nested-row, and `pstructural` proof chain has
  been removed from this file; `PStrong` is not used by the maintained
  factory proof.

  The development deliberately does not install a blanket Enum instance of
  `FreeOmegaDenotationBindLaws`.  Enum's omega relation is setwise
  convergence tested by Boolean predicates; on an unbounded carrier this
  alone does not justify convergence after binding an arbitrary varying
  kernel.  The factory instead proves the needed finite standard-transition
  coupling locally.  This keeps the analytic assumption at its true boundary
  and avoids strengthening the abstract measure interface unsoundly.
  The first compiled-shortcut removal is now checked at primitive finite
  fuel. `operational_vn_raw_round_observes` proves that the source
  `vn_step`, which really performs two biased samples, reaches exactly
  `vn_transition` after two primitive steps. At fuel one it observes only
  the zero subdistribution
  (`operational_vn_raw_round_one_observes_zero`), whereas the compiled
  one-sample round already observes `vn_transition`
  (`operational_vn_compiled_round_observes`). These facts unfold only the
  primitive kernel; they use no frontier or Iter rule.
  The scheduling mismatch is now lifted through the full unbounded program.
  `operational_vn_raw_hitting_three` derives the three-global-step recurrence
  (two samples plus the retry back-edge) directly from primitive hitting.
  The scheduled subsequence observes exactly the standard
  `meas_iter_approx` chain, and `operational_vn_raw_chains_cofinal` proves it
  cofinal with the complete global-fuel chain using hitting monotonicity.
  Consequently `operational_von_neumann_raw_ast` proves AST for the actual
  two-sample `von_neumann_third`, while
  `primitive_von_neumann_raw_direct_bisim` relates that source program
  directly to the one-sample terminating fair coin. The quotient step uses
  their common low-level Enum observation; it does not identify their
  differently shaped FreeOmega trees structurally.
  The outer example now makes its non-lockstep nature checkable:
  `operational_rational_coin_hitting_one` identifies the implementation's
  one-fuel primitive prefix, `operational_rational_direct_hitting_one`
  identifies the already-complete direct prefix, and
  `operational_rational_first_round_not_direct` proves their low-level Enum
  observations differ because the former has mass one half while the latter
  is total.  Their operational bisimulation is constructed through
  `operational_bisim_of_ast_lift`, so equality appears only at the AST limit.
- `FreeOmegaMeasure.v` now contains the nontrivial finite subbehavior order
  `free_omega_approx` (zero is bottom; Ret/Sample/Lub structure is preserved)
  and mutual eventual coverage `free_omega_chains_cofinal`.  The
  observation-closed quotient identifies formal lubs of such cofinal chains,
  with `free_omega_cofinal_lub_iff` deriving the corresponding semantic-lub
  equivalence. `Eq/OperationalProbabilisticPTSFreeOmega.v` lowers the former
  abstract Bind/Iter lub-cofinality premises to these concrete finite
  obligations.  The Ret-source Bind case is already discharged by
  `free_operational_bind_ret_approx_cofinal`; Tau/Prob and general iteration
  now reduce to finite fuel monotonicity and index-bound proofs rather than
  assumed weak-transition rules.
  FreeOmega's semantic order is no longer the placeholder `True`: both its
  structural and observation-closed omega interfaces use
  `free_omega_approx eq`.  Reflexivity, bottom, and continuation-bind
  monotonicity are proved structurally (`free_omega_approx_bind`), so the
  operational hitting-chain increasing theorem now carries genuine finite
  subbehavior content in the maintained unbounded backend.
  The order package now also includes transitivity and monotonicity of bind
  in its source distribution. `operational_hitting_mono` and
  `operational_bind_diagonal_mono` lift adjacent-fuel growth to arbitrary
  natural-number bounds.  Using these facts, the FreeOmega adequacy layer
  proves `free_operational_bind_tau_approx_cofinal`: if a Bind source has a
  finite cofinality certificate, adding a leading Tau preserves it via the
  explicit bounds `D n <= D_tau (n+1) <= D (n+1)`.  Thus Ret and Tau Bind
  cases are discharged constructively.  The stable Vis-source case is also
  pointwise identical at every fuel and is proved by
  `free_operational_bind_vis_approx_cofinal`.
  For Prob sources, `free_operational_bind_prob_uniform` states the exact
  generic requirement exposed by sampling: for each approximant there must
  be one almost-everywhere branch fuel bound in both directions.  The theorem
  `free_operational_bind_prob_approx_cofinal` proves this sufficient using
  restricted diagonal couplings.  On Enum, finite support supplies the
  uniform bound constructively by taking a `Nat.max` over the enumeration;
  `enum_free_operational_bind_prob_approx_cofinal` therefore derives the Prob
  case from ordinary pointwise branch cofinality. Ret, Vis, Tau, and Prob now
  all have compositional Bind-cofinality rules for the FreeOmega+Enum model;
  assembling them for arbitrary coinductive sources and proving iteration
  bounds remain.
  `operational_weak_iter` and `operational_ast_weak_iter` expose the
  iteration case independently of the structured frontier: a concrete client
  supplies only increasing round approximants, a round/primitive cofinality
  proof, the mixed-iteration limit, and (for AST) totality.  This is the entry
  point used for direct migration of fixed-cost unbounded samplers.

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
- `Examples/FiniteBindCounterexample.v` contains the concrete finite-layer
  divergence counterexample `finite_unrestricted_bind_congruence_fails`.
  Its scope is intentionally [apweak]; no stronger negative claim about the
  unified AST-aware relation is inferred from it.
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
  instance.  Its independent primitive-kernel counterpart is
  `primitive_biased_to_rational_coin_bisim_direct` in
  `Examples/OperationalBernoulliFactory.v`; the closed theorem
  `primitive_third_to_two_fifths_bisim_direct` compares the unbounded source
  implementation directly with the terminating target sampler.
- `Examples/RealBernoulliOracle.v` proves the oracle sampler's finite-prefix
  law and a uniform geometric vanishing bound for its missing mass.
  `Examples/RealBernoulliMathComp.v` then proves
  `mathcomp_binary_oracle_lub`: whenever those prefixes represent a real
  parameter `q`, the unbounded result measure is the genuine MathComp
  Bernoulli `q`; `mathcomp_binary_oracle_is_ast` proves AST.  This is the
  maintained real-valued behavioral result semantics.  The legacy single-HB
  `auweak` cannot host its recursive frontier, but the new two-level unified
  relation does; the corresponding weak-bisimulation and distribution-valued
  PTS theorems are documented below.
- `Eq/PWeakObservableEnum.v` proves Boolean return-event preservation from
  Enum couplings.  The Von Neumann and Bernoulli factory files instantiate it
  for the probability of returning `true`.

## MathComp Analysis boundary

- `Prob/MathCompMeasure.v` provides the measure, bind, subprobability, omega,
  and AST backend.  `MathCompCouplingGluing` is an explicit assumption because
  gluing is not a theorem of the bare measure interface on arbitrary types.
- `Prob/TwoLevelMeasureMathComp.v` now instantiates the low-universe `MN`
  interface with genuine MathComp kernels, including extensional equality,
  AE, coupling/gluing, setwise returned-mass order, lub, and totality.
  `Prob/FreeOmegaMeasure.v` supplies a separate universe-polymorphic formal
  behavior measure `MF`: MathComp samples remain low-universe nodes while
  results may contain recursive frontier heads at a higher universe.  Its
  structural coupling composes by the node backend's gluing law.  The
  maintained MathComp frontier uses the observation-closed relation
  `free_omega_qlift`: it is the least closure containing structural couplings
  and couplings of low-universe observations, and closed under composition,
  bind, mixed sampling, and formal lub.  Its extensional equality is therefore
  semantic equality-supported coupling rather than syntax equality.
  `SemanticMeasureAELiftLaws` isolates the diagonal-AE fact needed
  for Kleisli congruence; the MathComp adapter proves it from
  `almost_everywhere`, so FreeOmega provides checked AE bind, relational bind,
  and mixed-bind laws.
  `Examples/UnifiedMathCompFrontier.v` is the positive regression: a genuine
  MathComp Bernoulli node has a unified high-universe frontier and is
  reflexive under the new `weak_bisim` (assuming explicit MathComp gluing).
- `FreeOmega.free_omega_observes` folds a high-universe formal behavior into
  a low-universe node distribution.  Observable totality means that such a
  fold exists and its node distribution is total.  The strengthened
  `SemanticOmegaLaws` includes extensional chain properness, and
  `free_omega_observes_unique` proves that observation denotes at most one
  node distribution up to `sem_eq` whenever the node backend supplies that
  omega law and its bind laws.  In
  `Examples/UnifiedRealBernoulliMathComp.v`, every formal oracle approximant
  folds to the existing MathComp `meas_iter_approx`; the proved analytic lub
  is the genuine Bernoulli `q`, whose returned mass proves the `UFIter`
  totality premise.  Thus the real oracle has a checked unified AST frontier.
  The observation-closed coupling then relates that formal-lub frontier to
  the differently shaped direct-sample frontier.  The theorem
  `unified_mathcomp_binary_oracle_weak_bisim_direct` proves that the unbounded
  oracle program is weakly bisimilar to the terminating direct Bernoulli `q`
  program (assuming the explicit MathComp coupling-gluing capability).
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
  checked negative probe shows that the sealed monomorphic-universe
  `MathCompKernelMeasure` cannot itself be instantiated independently as both
  `MN` and `MF`.  The maintained free behavior layer is now the constructive
  resolution of that boundary.  The remaining negative regression explains
  why directly reusing HB at the frontier level is not
  yet enough: HB kernel operations and measurable instances already sealed
  below the recursive frontier cannot construct its measure.  The probe also
  asks HB to generate a new measurable carrier at an explicitly selected
  higher universe; MathComp's hierarchy constrains it back below the same
  global bound, so that local workaround is rejected as well.  End-to-end
  legacy single-backend MathComp `auweak` therefore needs a genuinely
  universe-polymorphic MathComp/HB hierarchy (likely an upstream change).
  The maintained two-level model avoids that boundary with its non-HB free
  frontier backend and now proves the real-valued program equivalence rather
  than assuming it.

## Deliberately deferred

- A new probabilistic refinement/simulation replacing legacy `PSSim`.
- Bidirectional ITree compilation bridges.
- Compatibility with every auxiliary rule of the legacy structural `equ`.
  The maintained hierarchy uses the smaller axiom-free `pstructural` instead.

The default validation command is:

```text
dune build -p coq-ptree @install
```
