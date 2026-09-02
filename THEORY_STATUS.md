# Maintained probabilistic equivalence theory

This file describes the maintained Coq API.  The named results are checked
without `Admitted` by the default `dune build`.

## Canonical semantics

PTree has one maintained probabilistic behavioral equivalence:

```text
PTree.observe
  -> ptree_primitive_kernel
  -> stable_hitting_approx
  -> stable_hitting_weak (subprobabilistic omega limit)
  -> sem_lift over stable Ret/Vis heads
  -> probabilistic_eutt / ≈ₚ (greatest fixed point)
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
- `probabilistic_eutt_coinduction_upto` and `stable_hitting_match_vis`;
- `probabilistic_eutt_coinduction_upto_bind` and
  `bind_upto_closure_compatible`;
- `stable_hitting_match_of_hitting_lift`;
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

## Equational and interpreter API

The FreeOmega theorem library is organized as a stable aggregate over five
focused public layers.  `ProbabilisticTrace` contains generic stable-head
and event-query laws; `OperationalProbabilisticPTSFreeOmegaFacts` contains
backend-specific operational facts; `...Rewrite` contains Monad/Functor laws
and setoid instances; `...Iter` contains iteration equations, fusion, and
Conway laws; and `...Interp` contains translation and effect-handler laws.
`OperationalProbabilisticPTSFreeOmega` re-exports these together with the
operational Base, preserving the historical import path and theorem names.

The canonical FreeOmega endpoint now includes all three Monad equations:

- `free_probabilistic_eutt_bind_ret_l`;
- `free_probabilistic_eutt_bind_ret_r`;
- `free_probabilistic_eutt_bind_assoc`.

The Functor surface is named explicitly rather than requiring clients to
unfold its monadic implementation:
`free_probabilistic_eutt_fmap_id`,
`free_probabilistic_eutt_fmap_compose`, and
`free_probabilistic_eutt_fmap_bind` provide identity, composition, and bind
naturality.

`probabilistic_eutt` is registered as an `Equivalence`.  Tau, Vis, and fixed
measure Prob constructors have `Proper` instances, and
`free_probabilistic_eutt_bind_Proper`,
`free_probabilistic_eutt_fmap_Proper`, and
`free_probabilistic_eutt_translate_Proper` support `setoid_rewrite` under
bind, mapping, and event renaming.
`semantic_lift_eq_Equivalence` registers coupling equality as a setoid, and
`probabilistic_eutt_prob_measure_Proper` lets `Prob` rewrite both its measure
and pointwise-related continuation.  The Enum regression rewrites a fair
distribution to a split-mass representation without requiring list
equality.
`Examples/ProbabilisticEuttAlgebra.v` checks these uses rather than merely
checking that the theorem names elaborate.

Iteration currently exposes canonical one-step unfolding and a
syntax-directed congruence:
`free_probabilistic_eutt_iter_unfold` and
`free_probabilistic_eutt_iter_structural`.  The more general
`free_probabilistic_eutt_iter_rel` is a heterogeneous relational-fusion law:
the loops may have different state and result types, provided related states
take `pstructural` steps whose sum results contain either related successor
states or related final results.  The countdown regression uses `nat` versus
`nat * unit` states and `nat` versus `bool` results.  Congruence is the
identity-relation instance.  Fusion from merely behavioral (rather than
structural) step hypotheses is now available for eventless unbounded loops:
`free_probabilistic_eutt_iter_behavioral_rel` chooses complete step hitting
witnesses, couples related steps, iterates those couplings over complete
rows, and uses the double-omega grid to obtain a heterogeneous loop
equivalence.  Its steps may have unrelated syntax and finite schedules.  The
retry regression moves Tau from outside a fair sample into every sampled
continuation; failed samples retry, so the loop has unboundedly many rounds.
The eventful generalization now has an explicit native proof boundary:
`free_iter_eventful_bisim_candidate` contains exactly related loop states,
and `free_probabilistic_eutt_iter_eventful_of_generator_closed` derives the
full behavioral fusion theorem from closure of that candidate under the
stable-hitting generator.  This removes the eventless scheduling machinery
from the remaining obligation.  As with generic effectful interpretation,
discharging it from behavioral step equivalence has the same remaining
stable-hitting companion issue as arbitrary effectful interpretation.  The
sound up-to-bind rule handles residual binds, but an internally returning
iteration step may collapse directly into the next recursive round before a
stable head is exposed.

Iteration naturality (the parameter identity) is now unconditional.
`pstructural_iter_natural` proves structurally that post-processing a loop
result with a Kleisli continuation is equivalent to pushing that
continuation into every successful step result;
`free_probabilistic_eutt_iter_natural` exports the canonical endpoint.  Its
regression uses a visible read followed by a fair probabilistic retry and a
Tau-producing postprocessor, so the law covers interaction and unbounded
execution rather than only finite countdowns.

The double-dagger/codiagonal identity is also proved structurally by
`pstructural_iter_codiagonal` and exported as
`free_probabilistic_eutt_iter_codiagonal`.  Its joint invariant distinguishes
the complete nested loop, an inner loop waiting for the outer handler, and
the flattened execution of a common step subtree.  The regression combines
a visible read with fair sampling so that both the inner-retry and
outer-retry branches can occur for unboundedly many rounds.

`PTree.interp` and its pure renaming instance `PTree.translate` are guarded
corecursive operations.  Interpretation inserts an administrative Tau at a
handled Vis.  `observe_interp` and the four shallow Ret/Tau/Vis/Prob equations
make this operational choice explicit.  `pstructural_interp` proves that an
arbitrary handler preserves structural equivalence, including handlers that
perform internal or visible target computation before returning.  Its
canonical FreeOmega endpoint is
`free_probabilistic_eutt_interp_structural`; canonical unfolding laws and
`free_probabilistic_eutt_translate_structural` are also exported.

`pstructural_interp_bind` uses a dedicated coinductive closure to track
handler execution together with bind reassociation.  It permits the handler
to run arbitrary target-side Tau/Vis/Prob structure before returning.
`free_probabilistic_eutt_interp_bind` exposes the resulting canonical monad
morphism equation, and `canonical_interp_bind_regression` checks it at the
Enum-to-FreeOmega endpoint.

The operational semantics now also has the missing general interpreter
composition theorem.  `operational_interp_diagonal_approx` first runs the
source to a stable Ret/Vis head and then runs the corresponding interpreted
head; `operational_weak_interp` lifts the two complete limits through mixed
bind.  For FreeOmega,
`free_operational_interp_approx_cofinal_all` proves that this diagonal chain
and direct `PTree.interp` execution are mutually cofinal for every source
tree and every effectful handler.  The finite schedules are `n` and `2*n`;
there is no AST, boundedness, or eventlessness premise.

`free_probabilistic_eutt_interp_of_head_lifts` is the corresponding
kernel-level preservation rule.  It takes one coupling of the completed
source heads and a coupling of the completed interpreted behavior of every
related head, then combines them with `FOQLBind` and concludes canonical
`probabilistic_eutt` for the whole interpreted programs.  Thus the remaining
fully generic preservation proof is isolated to constructing the guarded
family of per-head couplings; scheduling and limit composition are no longer
mixed into that coinductive argument.

Interpretation also commutes with guarded iteration.  The structural proof
`pstructural_interp_iter` uses one joint coinductive invariant containing the
main loop, the bind exposed by an unfolding, and the additional bind in
which an effectful handler may execute.  Its canonical endpoint is
`free_probabilistic_eutt_interp_iter`.  This law has no AST, finite-fuel, or
productivity premise: it reorganizes the same guarded computation rather
than evaluating a handler in advance.  `canonical_interp_iter_regression`
checks the law on an eventful loop whose handler inserts an administrative
Tau.

Sequential effect handlers also compose.  `pstructural_interp_compose`
tracks the two interpreters, the bind introduced by the first handler, and
the reassociation needed while the second handler executes;
`free_probabilistic_eutt_interp_compose` is its canonical endpoint.  Neither
handler is required to be pure.  The regression sends a source event through
a Tau/Vis-producing first handler and then replaces the intermediate Vis by
a Prob node in the second handler.

Handlers also support pointwise replacement at the structural baseline.
`pstructural_interp_handler` proves that structurally related handlers yield
structurally related interpretations, and
`free_probabilistic_eutt_interp_handler` exports the canonical endpoint.
The regression replaces a handler by a non-definitionally-equal version
containing a monadic redex under Tau.

Pure event renaming now has full behavioral preservation, not merely the
structural rule above.  `free_translate_approx_forward` and
`free_translate_approx_backward` account for the administrative Tau by
mutual finite-approximant inclusion.  `free_translate_hitting_cofinal` lifts
them through the FreeOmega cofinal quotient, and
`free_translate_hitting_lift` transports arbitrary complete hitting
witnesses.  `free_probabilistic_eutt_translate` then glues the left transport,
the source behavioral head coupling, and the right transport inside native
coinduction.  Its hypothesis is arbitrary `probabilistic_eutt`, not
`pstructural`.  The regression renames `sourceE` to a distinct `renamedE`
signature.

Identity interpretation is also a proved behavioral unit.
`free_probabilistic_eutt_translate_id` transports complete hitting behavior
on only the interpreted side and closes translated visible continuations by
native coinduction; `free_probabilistic_eutt_interp_trigger` exposes the law
as `interp trigger t ≈ₚ t`.  This cannot be a structural equation because
guarded interpretation inserts Tau before Vis.  The regression exercises an
actual visible `GetBit` event.

Pure renaming is functorial as well:
`free_probabilistic_eutt_translate_compose` proves
`translate g (translate f t) ≈ₚ translate (g ∘ f) t`.  Because two guarded
interpreters insert more Tau structure than one, this is proved by gluing
source-to-intermediate-to-left hitting transport with direct
source-to-right transport, not by structural equality.  The regression uses
three distinct event signatures (`AskBit`, `GetBit`, and `ReadBit`).

This is the first sound handler layer, not yet the full ITree-style claim
that `interp` preserves arbitrary `probabilistic_eutt`.  In particular,
effectful `interp` preservation for arbitrary behaviorally equivalent source
trees remains a future algebraic law; effectful-handler composition,
`interp_iter`, and pure `translate` preservation are complete.

The remaining law now has an exact generator-level interface in the focused
`OperationalProbabilisticPTSFreeOmegaInterp` module.
`free_interp_bisim_candidate` relates precisely interpretations of source
trees already related by `probabilistic_eutt`, and
`free_probabilistic_eutt_interp_of_generator_closed` proves full effectful
interpreter preservation from closure of that candidate.  Thus the open
proof obligation is specifically candidate-level closure of the binds
produced by handled visible heads; primitive scheduling, complete hitting,
and omega-limit composition are not part of the remaining gap.
The generic layer now includes a sound heterogeneous up-to-bind theorem.
`bind_upto_closure` contains the current candidate, the established greatest
fixed point, and binds whose continuations return to either relation;
`bind_upto_closure_compatible` proves generator compatibility without using
the final bind congruence, and
`probabilistic_eutt_coinduction_upto_bind` exposes the resulting proof rule.
This closes the previously missing bind-compatibility theorem itself.

It does not, by itself, prove arbitrary effectful interpretation.  When a
handled visible head returns internally, complete stable hitting immediately
continues into the interpreted source continuation before producing a stable
head.  Establishing the coupling for that collapsed segment asks recursively
for interpreter progress, rather than merely placing a residual visible
continuation in `bind_upto_closure`.  The remaining obligation is therefore
narrower: a guarded/companion closure for stable-hitting interpretation (or
an equivalent fusion theorem for this collapsed bind), not another measure
axiom and not ordinary bind compatibility.

Dirac elimination is now explicit rather than axiomatized accidentally.
`SemanticMeasureDiracAELaws` characterizes AE predicates on node Dirac
measures, while `MixedMeasureUnitLaws` states that mixed binding a node Dirac
is coupled to its selected continuation.  Under these capabilities,
`probabilistic_eutt_prob_ret` proves
`Prob (sem_ret x) k ≈ₚ k x`.  Enum supplies the exact Dirac AE law and the
FreeOmega observable quotient contains the corresponding
`FOQLSampleRetL` equation; `canonical_prob_ret_regression` checks the complete
Enum-to-FreeOmega instance chain.

Nested sampling is handled by a second optional capability,
`MixedMeasureNodeBindLaws`, which couples a node-level Kleisli bind with two
successive mixed binds.  Under it, `probabilistic_eutt_prob_flatten` proves
that two consecutive `Prob` nodes equal one node sampling the bound measure.
`SemanticMeasureBindAEExactLaws` supplies the additional reverse direction
of node-bind AE/support decomposition needed by a quotient backend.  Enum
proves it from nonzero finite-weight support decomposition.  The FreeOmega
observable quotient's `FOQLSampleBind` constructor is proved support-safe
from this exact law, yielding
`FreeOmegaObservableMixedMeasureNodeBindLaws`.  Consequently
`canonical_prob_flatten_regression` checks nested-Prob flattening at the
maintained Enum-to-FreeOmega canonical endpoint.

Independent sampling interchange is expressed by the optional relational
Fubini capability `MixedMeasureCommutativeLaws`.  Under that capability,
`probabilistic_eutt_prob_interchange` exchanges two nested `Prob` nodes with
dependent continuations by coupling their complete hitting limits.  A fixed
pair of measures may instead use `mixed_measure_exchange` and
`probabilistic_eutt_prob_interchange_of`.

For FreeOmega, `free_omega_ae_sample2_product_iff` identifies nested-sample
AE with product-node AE.  `free_omega_support_lift_sample_exchange` transports
that support through a product-swap coupling, and the guarded quotient rule
`FOQLSampleExchange` requires both this support witness and pointwise
continuation couplings.  `free_omega_mixed_exchange_of_product` packages the
result.  The Enum regression obtains its product coupling from finite
Fubini--Tonelli and proves canonical nested-Prob interchange end to end.
The law remains outside the base mixed interface, so noncommutative
measure-like effects remain admissible.

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

The PTree-facing guarded proof API also provides
`probabilistic_eutt_coinduction_upto`: recursive obligations may close either
in the user candidate or in an already established `probabilistic_eutt`.
`stable_hitting_match_vis` packages a common visible guard, including hitting
uniqueness and the Dirac head coupling.  On FreeOmega,
`free_stable_hitting_weak_bind_ret_only` composes an almost-everywhere
Ret-only closed sampler with an eventful continuation, while
`free_sem_lift_ret_bind_front` lifts its head coupling through those
continuations.  These are proof rules over the canonical semantics, not new
generator cases.

At the generator boundary, `stable_hitting_match_of_hitting_lift` turns two
complete hitting witnesses plus one coupling directly into the required
bidirectional match.  Hitting uniqueness performs both transports.  The
canonical endpoint rule `probabilistic_eutt_of_hitting_lift` and the
after-request phase of the interactive service are instances of this single
rule.

The former public relations `weak_bisim`, `unified_ppts_bisim`,
`operational_bisim`, `stable_kernel_bisim`, and `primitive_ptree_bisim`, plus
their proof/native full-abstraction and `BehavioralDomain` machinery, have
been removed.  `UnifiedPWeak.v`, `UnifiedPWeakTrans.v`,
`UnifiedProbabilisticPTS.v`, and their relation-specific examples no longer
exist.

The older `PWeak*` modules and their `apweak`, `auweak`, and `auequiv`
endpoints have now been removed.  Bernoulli, rational, and Von Neumann source
files retain only program definitions plus analytic convergence/AST
certificates; their behavioral theorems live in the corresponding
`Operational*` files and end in `probabilistic_eutt`.  The obsolete
`ProbabilisticPTS`, `UnifiedFrontierEnumFacts`, finite-bind counterexample,
and old MathComp factory client were removed with the closed legacy
dependency subgraph.

## Semantic regression examples

The maintained examples end directly in `probabilistic_eutt`:

- finite nested Enum sampling versus a merged sampler;
- binary rational sampling versus a direct rational coin;
- the unbounded Von Neumann sampler versus a one-step fair coin;
- an infinite request/reply service which runs that unbounded sampler between
  visible events, versus a service using one direct fair sample, together
  with a direct finite-cylinder probability theorem;
- the rational Bernoulli factory (including `1/3` to `2/5`) versus a direct
  target coin;
- the MathComp real-oracle Bernoulli sampler;
- a universe-polymorphic MathComp direct coin reflexivity regression.
- a fair half-return/half-silent-divergence program distinguished from a
  total return by its missing termination mass.

The Von Neumann proof compares independently established complete hitting
limits, so bounded and unbounded implementations do not share a mirrored
iteration design in the behavioral relation.

`Examples/InteractiveVonNeumannService.v` additionally demonstrates that
stable hitting is not a termination-only semantics.  Its two-state
coinduction candidate alternates between a stable `CoinRequest` head and an
unbounded AST sampling phase whose limit is coupled at `CoinReply`; each
reply continuation returns to the original pair of infinite services.  The
proof explicitly establishes Ret-only support almost everywhere before
binding the closed sampler into the eventful protocol.  It then uses the
generic Ret-only bind/lifting rules, guarded `Vis` matching, and coinduction
up to canonical equivalence; the example no longer reconstructs their
measure-level witnesses locally.

The same example now has an event-aware quantitative endpoint.  The generic
`ProbabilisticTrace` layer first classifies the next complete stable Ret/Vis
head and then extends this operation to finite interactive trace prefixes.
A selector has type `forall X, E X -> option X`: it recognizes the next
dependent event and supplies the environment response that enters its
continuation.  Recursive branch obligations are required almost everywhere
with respect to the stable-head measure, so inaccessible zero-mass branches
need no spurious hitting witness.

`finite_trace_query_singleton_iff_next_event_query` proves that the old
next-event query is precisely the singleton specialization.
`finite_trace_query_related` gives witness independence up to coupling, and
`probabilistic_eutt_preserves_finite_trace_query` proves that canonical
equivalence preserves every finite cylinder.  The proof uses coupling AE
transport and restriction at each prefix step; it is not a syntactic replay
of the two programs.

The certificate semantics is total on backends providing
`SemanticMeasureOrderLaws`: `finite_trace_query_exists` constructs a query by
induction over the finite prefix and uses `stable_hitting_weak_exists` at each
event boundary.  `finite_trace_query_unique_up_to_coupling` specializes the
relational theorem to reflexive `probabilistic_eutt`.  Classical choice then
packages `finite_trace_sem`, with `finite_trace_sem_spec` as its adequacy
contract and `probabilistic_eutt_preserves_finite_trace_sem` as its canonical
preservation theorem.  The generic result deliberately says `sem_lift eq`;
identifying that with `sem_eq` requires a backend equality-reflection law.

`request_true_reply_trace` directly represents the two-event prefix
`CoinRequest; CoinReply true` from the service root.
`direct_request_true_reply_prefix_query` identifies its direct-service query
with the previously computed `vn_fair` measure, and
`von_neumann_request_true_reply_probability_half` transports it to the
unbounded implementation.  The existing expectation theorem therefore reads
its true mass as `1/2`.
`direct_request_true_reply_sem_coupled_to_fair` connects the canonical
function to the explicit fair witness, while
`von_neumann_request_true_reply_sem_preserved` states preservation directly
between the two canonical denotations.  `direct_reply_first_prefix_rejected` checks a
non-matching first event.  Separately,
`canonical_spin_nonempty_trace_query_zero` proves that pure silent divergence
produces a zero-mass nonempty trace query, and
`divergent_trace_query_not_rejection_mass` distinguishes that missing mass
from an ordinary mass-one `false` result.

This is finite trace-prefix/cylinder semantics.  The maintained theory does
not claim a probability measure on infinite traces or a general WP calculus.

The artifact support range is Coq `>= 8.20` and `< 9.0`, with CI explicitly
installing Coq 8.20.1.  Coq 9 changes Stdlib load paths and requires a
separate migration; it is not part of the current compatibility claim.

## Exact no-Prob / ITree boundary

The maintained generic theorem deliberately does **not** claim

```text
probabilistic_eutt eq (embed t) (embed u) <-> eutt t u
```

under the current `SemanticMeasureInterface`.  The converse is not derivable
from these axioms and is false for admissible degenerate instances: the
interface gives positive coupling constructors and algebraic closure laws,
but it does not require couplings to separate unequal Dirac measures, reflect
zero mass, or invert a coupling of stable heads.  An implementation whose
`sem_lift` relates every pair satisfies the basic positive laws and makes
`probabilistic_eutt` universal, while ITree `eutt` is not universal.

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

The concrete FreeOmega/Enum audit narrows this further.  Its semantic lifting
is `free_omega_qlift`, and `free_omega_qlift_support` already recovers a
support coupling; Enum also proves zero-versus-Dirac mass separation.  Hence
the generic universal-coupling counterexample does not apply to this backend.
What is still absent is the pure-tree bridge itself: a maintained embedding
from ITree into no-`Prob` PTree, classification of its complete stable-hitting
limit through arbitrarily many Tau steps (including spin), and inversion of
the resulting supported stable-head coupling into ITree's dependent Vis
equality.  Until those three lemmas are formalized, the concrete iff is
plausible but unproved and is not exported as an artifact claim.
