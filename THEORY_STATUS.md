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

The following laws are checked:

- `probabilistic_eutt_equivalence` (`refl`, `sym`, and `trans`);
- `probabilistic_eutt_ret` and `probabilistic_eutt_vis`;
- `probabilistic_eutt_tau_l` and `probabilistic_eutt_tau_r`;
- `probabilistic_eutt_bind`;
- `probabilistic_eutt_preserves_hitting_mass`;
- `probabilistic_eutt_not_of_mass_mismatch`.

Tau invariance is derived from zero-prefix cofinality of the hitting chain.
Bind congruence is proved by a post-fixed candidate containing the existing
greatest fixed point and bind closure.  Bind is not a generator case.  The
current theorem consumes the established global/diagonal primitive-fuel
cofinality theorem as a proof-side scheduling fact.

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

The Von Neumann proof compares independently established complete hitting
limits, so bounded and unbounded implementations do not share a mirrored
iteration design in the behavioral relation.

## Remaining acceptance work

Two planned semantic conveniences remain open and are not claimed here:

1. an exact theorem relating the no-`Prob` embedding of ITree `eutt` to
   `probabilistic_eutt` (the Ret/Vis/Tau/bind fragment laws already hold);
2. one generic structured macro-kernel/corecursion proof rule from which
   `PTree.iter` can be obtained as an instance.

Neither item requires changing the canonical generator.  Future work must
strengthen hitting composition, structured certificates, or coinduction
up-to principles instead of adding syntax cases to `probabilistic_eutt`.
