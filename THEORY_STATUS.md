# Maintained probabilistic equivalence theory

This file describes the maintained Coq API on branch `new-idea`.  The named
results are checked without `Admitted` by the default `dune build`.

## Canonical semantics

PTree has one maintained probabilistic behavioral equivalence:

```text
PTree.observe
  -> ptree_primitive_kernel
  -> stable_hitting_approx
  -> stable_hitting_weak (subprobabilistic omega limit)
  -> sem_lift over stable Ret/Vis heads
  -> probabilistic_eutt / pbisim (greatest fixed point)
```

`Eq/PrimitiveStableHitting.v` contains the syntax-independent absorbing
hitting construction.  It defines finite approximants, their omega limit,
existence, uniqueness, increasingness, AE preservation, and AST as the
derived conjunction of weak hitting and `sem_total`.

`Eq/OperationalProbabilisticPTS.v` supplies the PTree primitive kernel.
The remaining `operational_target`, `operational_kernel`,
`operational_hitting_approx`, and `operational_weak` names are compatibility
aliases of the generic stable-target/kernel/hitting definitions; they no
longer form a second execution semantics.

`Eq/ProbabilisticEutt.v` defines the canonical coupling greatest fixed point.
Its generator contains only bidirectional matching of complete
stable-hitting limits through `sem_lift (head_rel sim)`.  It has no AST,
Step, Tau, Prob, Bind, Iter, frontier, or syntax-specific constructor.

The public notation is deliberately small:

```coq
t ≈ₚ u        (* probabilistic_eutt eq t u *)
t ≈ₚ[RR] u    (* probabilistic_eutt RR t u *)
```

Both notations live in `type_scope`, following ITree's relation-notation
convention.  Stable hitting, coupling, and frontier remain explicitly named
until their user-facing APIs stabilize further.

The following laws are checked:

- `probabilistic_eutt_equivalence` (`refl`, `sym`, and `trans`);
- `probabilistic_eutt_ret` and `probabilistic_eutt_vis`;
- `probabilistic_eutt_tau_l` and `probabilistic_eutt_tau_r`;
- `stable_hitting_weak_prob` and `probabilistic_eutt_prob`;
- `probabilistic_eutt_bind`;
- `stable_hitting_bisim_coinduction` and its PTree specialization
  `probabilistic_eutt_coinduction`;
- `probabilistic_eutt_of_iter_certificates`;
- `probabilistic_eutt_preserves_hitting_mass`;
- `probabilistic_eutt_not_of_mass_mismatch`.

Tau invariance is derived from zero-prefix cofinality of the hitting chain.
Bind congruence is proved by a post-fixed candidate containing the existing
greatest fixed point and bind closure.  Bind is not a generator case.  The
current theorem consumes the established global/diagonal primitive-fuel
cofinality theorem as a proof-side scheduling fact.

For the maintained FreeOmega backend this scheduling fact is now
unconditional, including eventful trees:
`free_operational_bind_approx_cofinal_all` proves mutual cofinality of the
global and diagonal chains, and `free_probabilistic_eutt_bind` exposes bind
as an unconditional monadic congruence.  A visible event is already a stable
head, so bind only rewrites its continuation and does not need to execute
through the event.  The former `no_event` theorem remains a compatibility
corollary of this stronger result.

`probabilistic_eutt_prob` is likewise derived at the hitting layer.  A
coupling of node measures and related branch bisimulations are composed with
`mixed_lift_bind`; probability sampling is not a generator constructor.

## Probability and missing mass

`Prob/TwoLevelMeasure.v` keeps node measures `MN` separate from behavioral
measures `MF`.  Coupling is the only probabilistic relation former.
`sem_same_mass mu nu` is the abstract total-subprobability-mass relation
defined by coupling under the total relation, and `sem_lift_same_mass` shows
that every semantic coupling preserves it.

`Prob/TwoLevelMeasureEnum.v` proves
`enum_sem_same_mass_zero_ret_bool`: the empty subdistribution cannot be
coupled with a Boolean point mass.  Together with
`probabilistic_eutt_not_of_mass_mismatch`, unequal termination probability is
observable and partial divergence cannot be silently identified with total
return.

It also proves `enum_sem_same_mass_expect_one`: indexed coupling preserves
the numeric total weight of arbitrary finite Enum measures, without an
`eqType` assumption on their values.  The program-level regression
`Examples/CanonicalPartialDivergence.v` uses this fact to prove
`1/2 Ret + 1/2 (Tau^omega)` is not canonically bisimilar to `Ret`.

The support-aware FreeOmega quotient and its AE, Kleisli, coupling, omega,
diagonal, and Fubini capabilities remain the maintained unbounded backend.
Enum and MathComp remain concrete instances of the generic measure API.

## Structured proof infrastructure

`Eq/UnifiedFrontier.v` defines stable heads, `frontier_head_rel`, and the
single structured `frontier` certificate.  Frontier is not a behavioral
equivalence.  `probabilistic_eutt_of_frontiers` first interprets two
frontiers as canonical primitive stable-hitting limits and then applies the
canonical coupling relation.

Finite computations and unbounded AST computations therefore use the same
`stable_hitting_weak`.  Bounded chains are special cases whose approximants
stabilize; AST is totality of the resulting limit rather than a bisimulation
constructor.

`stable_hitting_bisim_coinduction` is the public, syntax-independent corec
rule: every post-fixed stable-hitting candidate is contained in the
canonical greatest fixed point.  `probabilistic_eutt_of_iter_certificates`
is the `PTree.iter` instance.  It combines two `UFIter` certificates and a
coupling of their completed results; neither corecursion nor iteration adds
a case to the behavioral generator.  The formerly duplicated
`UFNestedIter` constructor has been removed.  Its compatibility use is a
derived lemma over `UFIter`.

The former public relations `weak_bisim`, `unified_ppts_bisim`,
`operational_bisim`, `stable_kernel_bisim`, and `primitive_ptree_bisim`, plus
their proof/native full-abstraction and `BehavioralDomain` machinery, have
been removed.  `UnifiedPWeak.v`, `UnifiedPWeakTrans.v`,
`UnifiedProbabilisticPTS.v`, and their relation-specific examples no longer
exist.

## Semantic regression examples

The maintained examples end directly in `probabilistic_eutt`:

- finite nested Enum sampling versus a merged sampler;
- binary rational sampling versus a direct rational coin;
- the unbounded Von Neumann sampler versus a one-step fair coin;
- the rational Bernoulli factory (including `1/3` to `2/5`) versus a direct
  target coin;
- the MathComp real-oracle Bernoulli sampler;
- a universe-polymorphic MathComp direct coin reflexivity regression.
- a fair half-return/half-silent-divergence program distinguished from a
  total return by its missing termination mass.

The Von Neumann proof compares independently established complete hitting
limits, so bounded and unbounded implementations do not share a mirrored
iteration design in the behavioral relation.

## Exact no-Prob / ITree boundary

The maintained generic theorem deliberately does **not** claim

```text
pbisim (embed t) (embed u) <-> eutt t u
```

under the current `SemanticMeasureInterface`.  The converse is not derivable
from these axioms and is false for admissible degenerate instances: the
interface gives positive coupling constructors and algebraic closure laws,
but it does not require couplings to separate unequal Dirac measures, reflect
zero mass, or invert a coupling of stable heads.  An implementation whose
`sem_lift` relates every pair satisfies the basic positive laws and makes
`pbisim` universal, while ITree `eutt` is not universal.

An exact backend-qualified correspondence therefore requires a separate
separation package with at least:

1. Dirac/Dirac coupling inversion and zero-versus-Dirac separation;
2. stable-head coupling inversion (including visible event equality and
   related continuations);
3. a pure-tree hitting classification: every no-`Prob` tree has either the
   zero divergent limit or a Dirac Ret/Vis stable limit, coherently through
   Tau;
4. the resulting pure-limit uniqueness/reflection theorem.

The already checked Ret, Vis, Tau, and bind laws give the sound structural
fragment in the forward direction.  Exact completeness belongs to a future
`SeparatingSemanticMeasure` backend theorem, not to the canonical generic
generator.  This boundary is intentional: strengthening the base interface
would incorrectly force Enum, MathComp, and future measure implementations
to expose representation-specific inversion principles as universal
probability axioms.
