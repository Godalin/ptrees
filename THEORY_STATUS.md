# Maintained probabilistic semantics

This file describes the maintained Coq API.  The named results are checked
without `Admitted` by the default `dune build`.

## Canonical architecture

PTree syntax is the intensional representation; stable hitting extracts its
extensional probabilistic behavior.  That behavior has a relational client
and a quantitative client:

```text
PTree syntax
  -> ptree_primitive_kernel
  -> stable_hitting_approx
  -> stable_hitting / H(t) (subprobabilistic omega limit)
       -> peutt / ≈ₚ (coupling greatest fixed point)
       -> finite_interaction_sem (finite cylinder observation)
```

`Eq/ProbabilisticSemantics.v` is the generic public facade for this graph.
It exposes curated notation and endpoint laws without transitively exporting
the proof-oriented implementation modules.  The current source tree contains
only the canonical relation and backend module names.

The canonical measure capabilities follow the same operations/laws split:
`SemanticMeasure`, `SemanticOmega`, and `MixedMeasure` contain structure,
while their property packages retain the `Laws` suffix.  The unrelated
legacy `MeasureInterface` name remains unchanged.

`SemanticMeasure` is deliberately measure-like rather than intrinsically
probabilistic: its relational algebra is also useful for unnormalised finite
weights.  Native probability is enforced by the concrete node carrier.
`SubEnum A` packages a raw finite rational `Enum A` with total weight at most
one, while `MathCompKernelMeasure` is intrinsically subprobabilistic.  Raw
`Enum` and its unrestricted `disc_score` form the raw weighted profile; they
must not be cited as enforcing the `Prob` contract.
`SemanticSubprobability` exposes the backend-specific validity predicate,
`SemanticSubprobabilityLaws` gives return/bind/equality closure, and
`SemanticSubprobabilityCarrierLaws` states that a carrier enforces validity
for every inhabitant.  Raw Enum deliberately lacks only the last package.

## Backend capability profiles

### FreeOmega limit-rule safety

The FreeOmega quotient lifting requires increasing chains when using
cofinality (`FOQLCofinal`), source/kernel diagonalization (`FOQLBindLub`),
and integration of pointwise limits (`FOQLSampleLub`).  Cofinality alone
does not identify limits of arbitrary sequences; support preservation alone
does not justify exchanging a limit with a changing kernel.  The instances
now pass the monotonicity premises already present in their capability
interfaces rather than discarding them.  Primitive hitting, bind/interp
diagonals, iteration grids, and sampler schedules discharge these premises
from their existing order theory.

Observation now enforces the same distinction between a formal omega
supremum and an arbitrary convergent sequence.  `FOOObserveLub` and
`FreeOmegaDenotationOmegaLaws` require the underlying FreeOmega chain to be
raw-increasing, not merely its finite-dimensional observable images to
converge.  This closes a concrete escape-mass construction missed by the
outer monotonicity checks alone: `FOLub (fun n => FORet n)` can be placed
inside a constant outer source chain, after which bind continuity exchanges
the order of two limits.  Keeping a permanent half-mass return makes both
outputs have identical support, so support transport does not reject the
construction.  With the former unrestricted observation rule, it yields
quotient equality between legitimate SubEnum behaviors of mass one and
one half.

`Examples/FreeOmegaEscapingMass.v` retains that derivation as a conditional
audit of the **former** rule (`unrestricted_observation_collapses_mass`),
not as an axiom or theorem asserting that the repaired backend collapses
mass.  `escaped_row_not_observable` rejects every observation of the
offending decreasing row under the repaired constructor;
`unrestricted_observation_rule_rejected` proves that the old rule cannot
be reinstated.  The earlier transient-atom audit likewise now rejects its
bad observation directly.  The subsequent scalar-model audit now also
proves preservation of all bounded tests, and hence total mass, for every
quotient constructor over SubEnum; see `FreeOmegaUpperQuotientSubEnum.v`.
The positive regression `increasing_kernel_observable` observes the
increasing direction of the same grid without the former rule.  Existing
RandomWalk, Von Neumann, Bernoulli-factory, and MathComp oracle observations
discharge the new premise from their increasing approximation schedules.

`Examples/FreeOmegaLimitSafety.v` records the rejected decreasing-mass and
moving-diagonal inputs.  The former uses a valid mass-one coin and compares
mass one with mass two thirds, so this is not a raw-weight validity issue.
These tests repair the identified rule-boundary vulnerabilities.  The newer
bounded-test model covers the complete SubEnum quotient, but is not an
additive measure model for arbitrary non-increasing raw Lub expressions.
The unrestricted residual GFP is now sound over SubEnum/FreeOmega, through
actual finite transport rather than an assumed extension of unary-policy
acceleration.  This does not establish the same theorem for every backend.

`Examples/BackendCapabilities.v` is the compile-time audit of the bounded
finite profile, the raw weighted compatibility profile, and the MathComp
profile:

```text
SubEnum node           -> FreeOmega SubEnum behavior
Enum node (weighted)   -> FreeOmega Enum behavior
MathComp kernel node   -> FreeOmega MathCompKernelMeasure behavior
```

Capabilities are assigned to the layer where they mathematically belong;
the goal is not to make the two node layers superficially identical.

| Capability | SubEnum node | raw Enum node | MathComp node | FreeOmega behaviors |
| --- | --- | --- | --- | --- |
| total weight `<= 1` | by carrier | not enforced | by carrier | inherited denotationally |
| `SemanticMeasure`, core, AE lift | direct | direct | direct¹ | derived/direct |
| AE Kleisli, Dirac AE, countable AE | direct | direct | direct | derived |
| coupling AE | direct | direct | direct | derived |
| bind-AE exactness | direct | direct | direct | used to derive mixed node-bind |
| `SemanticMeasureBindLaws` | direct | direct | not required² | direct FreeOmega proof |
| omega order/laws/cofinality | node-specific subset | node-specific subset | node-specific subset | derived |
| omega AE, diagonal, Fubini | — | — | — | derived |
| mixed laws/unit/node-bind/omega | — | — | — | derived |
| mixed commutativity | optional | optional | optional | not required |

¹ MathComp's core relational package keeps `MathCompCouplingGluing` explicit,
because coupling composition is not available for arbitrary full-powerset
measures without an additional gluing assumption.

² The missing node-level field is relational coupling through kernel bind.
The maintained behavioral measure already has `SemanticMeasureBindLaws` by
FreeOmega construction.  Adding the node instance would require a new
measurable joint-kernel selection/gluing development, so it is intentionally
not pursued merely for matrix symmetry.

The MathComp AE adapters use existing measure facts: negligible sets are
closed under countable union, Dirac AE is exact, kernel bind is integration,
and a nonnegative integral is zero exactly almost everywhere.  Consequently
the node instances automatically unlock FreeOmega coupling AE, omega AE,
diagonal continuity, Fubini, mixed unit, and nested-`Prob` flattening.

`Eq/PrimitiveStableHitting.v` contains the syntax-independent absorbing
hitting construction.  It defines finite approximants, their omega limit,
existence, uniqueness, increasingness, AE preservation, and AST as the
derived conjunction of stable hitting and `sem_total`.  `stable_hitting` is
the canonical public name.

`Eq/PTreeKernel.v` supplies the PTree adapter to the generic construction:
`ptree_primitive_kernel`, `ptree_hitting_approx`, and
`ptree_stable_hitting`.  These are PTree-specialized definitions over the
single generic stable-hitting semantics, not a second execution semantics.

`Eq/PEutt.v` defines the canonical coupling greatest fixed point.
Its generator contains only bidirectional matching of complete
stable-hitting limits through `sem_lift (head_rel sim)`.  It has no AST,
Step, Tau, Prob, Bind, Iter, certificate, or syntax-specific constructor.

Stable observations are called `stable_head` and related by
`stable_head_rel`.  The syntax-directed `frontier_certificate` judgment is
proof infrastructure for constructing stable-hitting facts, not a second
operational or behavioral semantics.

The public notation is deliberately small:

```coq
t ≈ₚ u        (* peutt eq t u *)
t ≈ₚ[RR] u    (* peutt RR t u *)
```

Both notations live in `type_scope`, following ITree's relation-notation
convention.  `peutt` is the only public behavioral relation;
the maintained proof hierarchy below it is

```text
pstruct ⊆ pstrong ⊆ pfinite ⊆ peutt.
```

`pstruct` is exact structural lockstep.  `pstrong` uses the canonical
`SemanticMeasure` coupling while retaining lockstep control flow;
`pstrong_bind` threads a heterogeneous coupling through monadic composition.
The heterogeneous `pfinite_rel` alternates well-founded internal Tau/Prob
compression with one guarded `pstrongF` match.  Compression stops at residual
trees, not necessarily stable heads, and has no fuel or omega interface.
An infinite one-sided silent loop cannot justify an arbitrary relation.
The public homogeneous `pfinite` is the finite reflexive-symmetric-transitive
closure of this GFP.  Consequently
`pfinite_refl`, `pfinite_sym`, `pfinite_trans`, and
`pfinite_equivalence` are available without introducing any omega execution
rule.  `Eq/FreeOmega/FiniteInternalTransport.v` proves soundness first for
`pfinite_rel` and then for the equivalence closure, under the explicit native
coupling-realization capability proved for SubEnum.  Raw Enum and MathComp
do not currently instantiate this optional capability.  `Relation.v`
registers the corresponding conditional `subrelation` instances.  `PEutt.v`
supplies generic endpoint rewriting for every registered stronger relation.

The following laws are checked:

- `peutt_equivalence` (`refl`, `sym`, and `trans`);
- `peutt_ret` and `peutt_vis`;
- `peutt_tau_l` and `peutt_tau_r`;
- `stable_hitting_prob` and `peutt_prob`;
- `peutt_bind`;
- `stable_hitting_bisim_coinduction` and its PTree specialization
  `peutt_coinduction`;
- `peutt_coinduction_upto` and `stable_hitting_match_vis`;
- `peutt_coinduction_upto_bind` and
  `bind_upto_closure_compatible`;
- `stable_hitting_match_of_hitting_lift`;
- `peutt_of_iter_certificates`;
- `peutt_preserves_hitting_mass`;
- `peutt_not_of_mass_mismatch`.

Tau invariance is derived from zero-prefix cofinality of the hitting chain.
Bind congruence is proved by a post-fixed candidate containing the existing
greatest fixed point and bind closure.  Bind is not a generator case.  The
current theorem consumes the established global/diagonal primitive-fuel
cofinality theorem as a proof-side scheduling fact.

For the maintained FreeOmega backend this scheduling fact is now
unconditional, including eventful trees:
`FreeOmega.Bind.ptree_bind_approx_cofinal_all` proves mutual cofinality of the
global and diagonal chains, and `FreeOmega.Bind.peutt_bind` exposes bind
as an unconditional monadic congruence.  A visible event is already a stable
head, so bind only rewrites its continuation and does not need to execute
through the event.  The eventless theorem is a restricted corollary of this
stronger result.

`peutt_prob` is likewise derived at the hitting layer.  A
coupling of node measures and related branch bisimulations are composed with
`mixed_lift_bind`; probability sampling is not a generator constructor.

## Equational and interpreter API

The FreeOmega theorem library is organized by responsibility under
`Eq/FreeOmega/`: `Base` contains approximant and translation foundations,
`Relation` proves soundness of the relation hierarchy, `Bind` contains
diagonal scheduling and composition infrastructure, `Algebra` contains
Monad/Functor laws and setoid instances, `Iter` contains iteration equations
and fusion, and `Interp` contains translation and effect-handler laws.
`Eq/FreeOmega.v` is the canonical aggregate.  Enum-only finite-support
cofinality lives separately in `Prob/EnumCofinality.v`.

The canonical FreeOmega endpoint now includes all three Monad equations:

- `FreeOmega.Algebra.peutt_bind_ret_l`;
- `FreeOmega.Algebra.peutt_bind_ret_r`;
- `FreeOmega.Algebra.peutt_bind_assoc`.

The Functor surface is named explicitly rather than requiring clients to
unfold its monadic implementation:
`peutt_fmap_id`,
`peutt_fmap_compose`, and
`peutt_fmap_bind` provide identity, composition, and bind
naturality.

`peutt` is registered as an `Equivalence`.  Tau, Vis, and fixed
measure Prob constructors have `Proper` instances, and
`peutt_bind_Proper`,
`peutt_fmap_Proper`, and
`peutt_translate_Proper` support `setoid_rewrite` under
bind, mapping, and event renaming.
`semantic_lift_eq_Equivalence` registers coupling equality as a setoid, and
`peutt_prob_measure_Proper` lets `Prob` rewrite both its measure
and pointwise-related continuation.  The Enum regression rewrites a fair
distribution to a split-mass representation without requiring list
equality.
`Examples/PEuttAlgebra.v` checks these uses rather than merely
checking that the theorem names elaborate.

Iteration currently exposes canonical one-step unfolding and a
syntax-directed congruence:
`peutt_iter_unfold` and
`peutt_iter_structural`.  The more general
`peutt_iter_rel` is a heterogeneous relational-fusion law:
the loops may have different state and result types, provided related states
take `pstruct` steps whose sum results contain either related successor
states or related final results.  The countdown regression uses `nat` versus
`nat * unit` states and `nat` versus `bool` results.  Congruence is the
identity-relation instance.  Fusion from merely behavioral (rather than
structural) step hypotheses is now available for eventless unbounded loops:
`peutt_iter_behavioral_rel` chooses complete step hitting
witnesses, couples related steps, iterates those couplings over complete
rows, and uses the double-omega grid to obtain a heterogeneous loop
equivalence.  Its steps may have unrelated syntax and finite schedules.  The
retry regression moves Tau from outside a fair sample into every sampled
continuation; failed samples retry, so the loop has unboundedly many rounds.
The eventful generalization now has an explicit native proof boundary:
`iter_eventful_bisim_candidate` contains exactly related loop states,
and `peutt_iter_eventful_of_generator_closed` derives the
full behavioral fusion theorem from closure of that candidate under the
stable-hitting generator.  This removes the eventless scheduling machinery
from the remaining obligation.  As with generic effectful interpretation,
discharging it from behavioral step equivalence has the same remaining
stable-hitting companion issue as arbitrary effectful interpretation.  The
sound up-to-bind rule handles residual binds, but an internally returning
iteration step may collapse directly into the next recursive round before a
stable head is exposed.

Iteration naturality (the parameter identity) is now unconditional.
`pstruct_iter_natural` proves structurally that post-processing a loop
result with a Kleisli continuation is equivalent to pushing that
continuation into every successful step result;
`peutt_iter_natural` exports the canonical endpoint.  Its
regression uses a visible read followed by a fair probabilistic retry and a
Tau-producing postprocessor, so the law covers interaction and unbounded
execution rather than only finite countdowns.

The double-dagger/codiagonal identity is also proved structurally by
`pstruct_iter_codiagonal` and exported as
`peutt_iter_codiagonal`.  Its joint invariant distinguishes
the complete nested loop, an inner loop waiting for the outer handler, and
the flattened execution of a common step subtree.  The regression combines
a visible read with fair sampling so that both the inner-retry and
outer-retry branches can occur for unboundedly many rounds.

`PTree.interp` and its pure renaming instance `PTree.translate` are guarded
corecursive operations.  Interpretation inserts an administrative Tau at a
handled Vis.  `observe_interp` and the four shallow Ret/Tau/Vis/Prob equations
make this operational choice explicit.  `pstruct_interp` proves that an
arbitrary handler preserves structural equivalence, including handlers that
perform internal or visible target computation before returning.  Its
canonical FreeOmega endpoint is
`peutt_interp_structural`; canonical unfolding laws and
`peutt_translate_structural` are also exported.

`pstruct_interp_bind` uses a dedicated coinductive closure to track
handler execution together with bind reassociation.  It permits the handler
to run arbitrary target-side Tau/Vis/Prob structure before returning.
`peutt_interp_bind` exposes the resulting canonical monad
morphism equation, and `canonical_interp_bind_regression` checks it at the
Enum-to-FreeOmega endpoint.

The operational semantics now also has the missing general interpreter
composition theorem.  `ptree_interp_diagonal_approx` first runs the
source to a stable Ret/Vis head and then runs the corresponding interpreted
head; `ptree_stable_hitting_interp` lifts the two complete limits through mixed
bind.  For FreeOmega,
`ptree_interp_approx_cofinal_all` proves that this diagonal chain
and direct `PTree.interp` execution are mutually cofinal for every source
tree and every effectful handler.  The finite schedules are `n` and `2*n`;
there is no AST, boundedness, or eventlessness premise.

`peutt_interp_of_head_lifts` is the corresponding
kernel-level preservation rule.  It takes one coupling of the completed
source heads and a coupling of the completed interpreted behavior of every
related head, then combines them with `FOQLBind` and concludes canonical
`peutt` for the whole interpreted programs.  Thus the remaining
fully generic preservation proof is isolated to constructing the guarded
family of per-head couplings; scheduling and limit composition are no longer
mixed into that coinductive argument.

Interpretation also commutes with guarded iteration.  The structural proof
`pstruct_interp_iter` uses one joint coinductive invariant containing the
main loop, the bind exposed by an unfolding, and the additional bind in
which an effectful handler may execute.  Its canonical endpoint is
`peutt_interp_iter`.  This law has no AST, finite-fuel, or
productivity premise: it reorganizes the same guarded computation rather
than evaluating a handler in advance.  `canonical_interp_iter_regression`
checks the law on an eventful loop whose handler inserts an administrative
Tau.

Sequential effect handlers also compose.  `pstruct_interp_compose`
tracks the two interpreters, the bind introduced by the first handler, and
the reassociation needed while the second handler executes;
`peutt_interp_compose` is its canonical endpoint.  Neither
handler is required to be pure.  The regression sends a source event through
a Tau/Vis-producing first handler and then replaces the intermediate Vis by
a Prob node in the second handler.

Handlers also support pointwise replacement at the structural baseline.
`pstruct_interp_handler` proves that structurally related handlers yield
structurally related interpretations, and
`peutt_interp_handler` exports the canonical endpoint.
The regression replaces a handler by a non-definitionally-equal version
containing a monadic redex under Tau.

Pure event renaming now has full behavioral preservation, not merely the
structural rule above.  `translate_approx_forward` and
`translate_approx_backward` account for the administrative Tau by
mutual finite-approximant inclusion.  `translate_hitting_cofinal` lifts
them through the FreeOmega cofinal quotient, and
`translate_hitting_lift` transports arbitrary complete hitting
witnesses.  `peutt_translate` then glues the left transport,
the source behavioral head coupling, and the right transport inside native
coinduction.  Its hypothesis is arbitrary `peutt`, not
`pstruct`.  The regression renames `sourceE` to a distinct `renamedE`
signature.

Identity interpretation is also a proved behavioral unit.
`peutt_translate_id` transports complete hitting behavior
on only the interpreted side and closes translated visible continuations by
native coinduction; `peutt_interp_trigger` exposes the law
as `interp trigger t ≈ₚ t`.  This cannot be a structural equation because
guarded interpretation inserts Tau before Vis.  The regression exercises an
actual visible `GetBit` event.

Pure renaming is functorial as well:
`peutt_translate_compose` proves
`translate g (translate f t) ≈ₚ translate (g ∘ f) t`.  Because two guarded
interpreters insert more Tau structure than one, this is proved by gluing
source-to-intermediate-to-left hitting transport with direct
source-to-right transport, not by structural equality.  The regression uses
three distinct event signatures (`AskBit`, `GetBit`, and `ReadBit`).

This is a sound handler layer, not an unconditional ITree-style claim that
`interp` preserves arbitrary `peutt`.  Effectful-handler
composition, `interp_iter`, and pure `translate` preservation are complete.

The remaining law now has an exact generator-level interface in
`Eq/FreeOmega/Interp.v`.
`interp_bisim_candidate` relates precisely interpretations of source
trees already related by `peutt`, and
`peutt_interp_of_generator_closed` proves full effectful
interpreter preservation from closure of that candidate.  Thus the open
proof obligation is specifically candidate-level closure of the binds
produced by handled visible heads; primitive scheduling, complete hitting,
and omega-limit composition are not part of the remaining gap.
The generic layer now includes a sound heterogeneous up-to-bind theorem.
`bind_upto_closure` contains the current candidate, the established greatest
fixed point, and binds whose continuations return to either relation;
`bind_upto_closure_compatible` proves generator compatibility without using
the final bind congruence, and
`peutt_coinduction_upto_bind` exposes the resulting proof rule.
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

The bounded audit now exposes that last premise directly.
`interp_vis_fusion` asks only for generator progress of a pair of
handled `Vis` heads whose source continuations are pointwise canonically
equivalent.  `peutt_interp_of_vis_fusion` proves full
effectful `interp` preservation from it, deriving source hitting, Ret-head
matching, outer interpreter cofinality, and coupling composition from the
maintained library.  This is strictly narrower than the older whole-
candidate `interp_generator_closed` interface.  Proving it from the
ordinary bind companion would require using the very interpreter-progress
claim being established after an internally returning handler crosses into
the source continuation, hence an unguarded self-use.  The artifact records
this as the exact research boundary and does not expand the core scope to
postulate a stronger measure law.

Dirac elimination is now explicit rather than axiomatized accidentally.
`SemanticMeasureDiracAELaws` characterizes AE predicates on node Dirac
measures, while `MixedMeasureUnitLaws` states that mixed binding a node Dirac
is coupled to its selected continuation.  Under these capabilities,
`peutt_prob_ret` proves
`Prob (sem_ret x) k ≈ₚ k x`.  Enum supplies the exact Dirac AE law and the
FreeOmega observable quotient contains the corresponding
`FOQLSampleRetL` equation; `canonical_prob_ret_regression` checks the complete
raw Enum-to-FreeOmega compatibility chain.  The bounded SubEnum chain is
checked independently in `SubEnumRegression.v`.

Nested sampling is handled by a second optional capability,
`MixedMeasureNodeBindLaws`, which couples a node-level Kleisli bind with two
successive mixed binds.  Under it, `peutt_prob_flatten` proves
that two consecutive `Prob` nodes equal one node sampling the bound measure.
`SemanticMeasureBindAEExactLaws` supplies the additional reverse direction
of node-bind AE/support decomposition needed by a quotient backend.  Enum
proves it from nonzero finite-weight support decomposition.  The FreeOmega
observable quotient's `FOQLSampleBind` constructor is proved support-safe
from this exact law, yielding
`FreeOmegaObservableMixedMeasureNodeBindLaws`.  Consequently
`canonical_prob_flatten_regression` checks nested-Prob flattening at the
raw Enum-to-FreeOmega compatibility endpoint; the same capability is
machine-audited for the canonical bounded SubEnum endpoint.

Independent sampling interchange is expressed by the optional relational
Fubini capability `MixedMeasureCommutativeLaws`.  Under that capability,
`peutt_prob_interchange` exchanges two nested `Prob` nodes with
dependent continuations by coupling their complete hitting limits.  A fixed
pair of measures may instead use `mixed_measure_exchange` and
`peutt_prob_interchange_of`.

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
measures `MF`.  Coupling is the relational measure former.
`sem_same_mass mu nu` is abstract equality of total semantic weight, defined
by coupling under the total relation; on SubEnum and MathComp this is equality
of subprobability mass.  `sem_lift_same_mass` shows that every semantic
coupling preserves it.  Coupling equality alone does not provide an upper
bound, which is why the probability constraint is enforced by the node
carrier rather than inferred from the generic relation.

`Prob/TwoLevelMeasureEnum.v` proves
`enum_sem_same_mass_zero_ret_bool`: the empty subdistribution cannot be
coupled with a Boolean point mass.  Together with
`peutt_not_of_mass_mismatch`, unequal termination probability is
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

`Eq/UnifiedFrontier.v` defines stable heads, `stable_head_rel`, and the
single structured `frontier_certificate` judgment.  It is not a behavioral
equivalence.  `peutt_of_frontiers` first interprets two certificates as
canonical primitive stable-hitting limits and then applies the
canonical coupling relation.

Finite computations and unbounded AST computations therefore use the same
`stable_hitting`.  Bounded chains are special cases whose approximants
stabilize; AST is totality of the resulting limit rather than a bisimulation
constructor.

`stable_hitting_bisim_coinduction` is the public, syntax-independent corec
rule: every post-fixed stable-hitting candidate is contained in the
canonical greatest fixed point.  `peutt_of_iter_certificates`
is the `PTree.iter` instance.  It combines two `UFIter` certificates and a
coupling of their completed results; neither corecursion nor iteration adds
a case to the behavioral generator.  The formerly duplicated
`UFNestedIter` constructor has been removed.  Its compatibility use is a
derived lemma over `UFIter`.

The PTree-facing guarded proof API also provides
`peutt_coinduction_upto`: recursive obligations may close either
in the user candidate or in an already established `peutt`.
`stable_hitting_match_vis` packages a common visible guard, including hitting
uniqueness and the Dirac head coupling.  On FreeOmega,
`free_stable_hitting_bind_ret_only` composes an almost-everywhere
Ret-only closed sampler with an eventful continuation, while
`free_sem_lift_ret_bind_front` lifts its head coupling through those
continuations.  These are proof rules over the canonical semantics, not new
generator cases.

At the generator boundary, `stable_hitting_match_of_hitting_lift` turns two
complete hitting witnesses plus one coupling directly into the required
bidirectional match.  Hitting uniqueness performs both transports.  The
canonical endpoint rule `peutt_of_hitting_lift` and the
after-request phase of the interactive service are instances of this single
rule.

The former public relations `weak_bisim`, `unified_ppts_bisim`,
`ptree_bisim`, `stable_kernel_bisim`, and `primitive_ptree_bisim`, plus
their proof/native full-abstraction and `BehavioralDomain` machinery, have
been removed.  `UnifiedPWeak.v`, `UnifiedPWeakTrans.v`,
`UnifiedProbabilisticPTS.v`, and their relation-specific examples no longer
exist.

The older `PWeak*` modules and their `apweak`, `auweak`, and `auequiv`
endpoints have now been removed.  Bernoulli, rational, and Von Neumann source
files retain only program definitions plus analytic convergence/AST
certificates; their behavioral theorems live in the corresponding
`Operational*` files and end in `peutt`.  The obsolete
`ProbabilisticPTS`, `UnifiedFrontierEnumFacts`, finite-bind counterexample,
and old MathComp factory client were removed with the closed legacy
dependency subgraph.

## Semantic regression examples

The maintained examples end directly in `peutt`:

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

`Examples/BernoulliFactoryComposition.v` adds a parametric compositional
endpoint. The sampler is an explicit argument of `factory_with_sampler`;
its congruence theorem uses `peutt_bind` and
`peutt_iter_behavioral_rel` for the empty event signature.
The VN-to-fair theorem proves the support coupling for arbitrary normalized,
nondegenerate rational source weights. The fair factory is related to the
standard binary loop, then to direct sampling. The final VN factory theorem
uses `peutt_trans` through the fair factory without either
example-specific support premise. `OperationalFactoryRationalSupportLaws`
has been replaced by a proved `ptree_factory_standard_q_support`.
The legacy monolithic route still takes `OperationalFactoryStepSupportLaws`;
the compositional endpoint does not. A Tau-sampler regression checks that
the congruence is behavioral rather than syntactic. Operational component
proofs now live in `OperationalBernoulliFactory.v`, leaving composition and
probability-algebra rewriting in `BernoulliFactoryComposition.v`.

The support proof uses `enum_converges_ae_iff` in `Prob/EnumSupport.v`:
for increasing Enum chains over decidable-equality outcomes, AE at the limit
is equivalent to AE at every finite approximation. The proof extracts
positive singleton support constructively, without classical predicate choice. `enum_iter_approx_increasing` establishes the premise
for any absorbing Enum iteration, without a normalization assumption.
`free_omega_support_lift_observation_ae` in `Prob/FreeOmegaSupport.v` then
recovers high-universe support from an observation coupling and AE
preservation/reflection. Equal observations and injectivity alone cannot do
this: the transient-atom counterexample is nonmonotone and remains invalid.
No generic observation-completeness axiom has been introduced.

`Examples/BernoulliFactoryProbability.v` certifies raw Enum source samplers,
Factory contexts, composed programs, and direct coins as
`probabilistic_ptree`. The source certificate needs normalization only;
the context certificate works for any event signature and any well-formed
Boolean sampler. Nondegeneracy and termination belong to behavioral
correctness, not to the syntax-level probability contract.

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

`Examples/MixedHeadProtocol.v` adds a focused probabilistic-LTS example
on `SubEnum`/`FreeOmega SubEnum`. The implementation's single hidden bit and
the environment's challenge parameterize a two-to-one map from independent
bits r (fair), s (P(true)=3/4), and h (fair) to four Stop/Continue outcomes:
q=m xor r selects the head kind and b=c xor s the output.
`mixed_encode_fiber` identifies exactly the two h-preimages of each outcome.
`mixed_triple_outcome_lift` exhibits the eight-atom joint distribution and
sums its preimage masses to the challenge-dependent target weights.
`masked_head_stop_h` discards h on return, while `masked_head_continue_h`
retains it in the continuation. Thus eight sampled atoms yield six concrete
head forms, coupled to four abstract heads by `mixed_heads_lift`. Each
matched Reply demands the simulation for every acknowledgement; the next
hidden state is h on ack=true and r on ack=false.
`mixed_protocol_sim_postfixed` uses Root/After phases, and
`masked_protocol_equivalent` applies plain `peutt_coinduction`.
`masked_after_heads_denote_four` exposes the challenge-dependent stable-head
observation extensionally; `masked_after_stable_hitting` ties it to the
implementation's complete-hitting witness.
`masked_challenge_true_reply_probability` gives probability `3/8` for
challenge false and `1/8` for challenge true, using finite-cylinder preservation and the
SubEnum probability API. No example-specific assumptions or up-to closure
are used. Event responses use a universe-polymorphic two-value wrapper
around bool, preserving both genuine environment choices in PTree's
invariant event universe.

This first eventful client of `ProbabilisticTraceSubEnum.v` also exposed
monomorphic universe constraints in its public probability wrapper. The
module now enables universe polymorphism, matching `ProbabilisticTraceEnum`
and allowing the canonical eventful proof witnesses to instantiate it.

The same example now has an event-aware quantitative endpoint.  The generic
`ProbabilisticTrace` layer first classifies the next complete stable Ret/Vis
head and then extends this operation to finite interaction patterns.
A selector has type `forall X, E X -> option X`: it recognizes the next
dependent event and supplies the environment response that enters its
continuation.  Recursive branch obligations are required almost everywhere
with respect to the stable-head measure, so inaccessible zero-mass branches
need no spurious hitting witness.

The type `finite_interaction_pattern` is a list of selectors.  Because a
selector may accept several events, such a pattern denotes a finite
prefix/cylinder observation and is not necessarily one concrete trace;
singleton selectors recover ordinary concrete traces.

`finite_interaction_query_singleton_iff_next_event_query` proves that the old
next-event query is precisely the singleton specialization.
`finite_interaction_query_related` gives witness independence up to coupling, and
`peutt_preserves_finite_interaction_query` proves that canonical
equivalence preserves every finite cylinder.  The proof uses coupling AE
transport and restriction at each prefix step; it is not a syntactic replay
of the two programs.

The certificate semantics is total on backends providing
`SemanticMeasureOrderLaws`: `finite_interaction_query_exists` constructs a query by
induction over the finite prefix and uses `stable_hitting_exists` at each
event boundary.  `finite_interaction_query_unique_up_to_coupling` specializes the
relational theorem to reflexive `peutt`.  Classical choice then
packages `finite_interaction_sem`, with
`finite_interaction_sem_spec` as its adequacy contract and
`peutt_preserves_finite_interaction_sem` as its canonical preservation
theorem.  The generic result deliberately says `sem_lift eq`;
identifying that with `sem_eq` requires a backend equality-reflection law.

`ProbabilisticTraceEnum` adds the concrete presentation layer without
duplicating this generic semantics.  `enum_finite_interaction_probability`
and the notation
`Prₜ[t | pattern] = p` require a valid generic query, an observational
FreeOmega representative coupled to it, a concrete Enum denotation, and the
rational expectation of the Boolean indicator.  Consequently the numeric
API respects the semantic quotient and never computes by inspecting the
arbitrary representative selected by classical choice.

`request_true_reply_trace` directly represents the two-event prefix
`CoinRequest; CoinReply true` from the service root.
`direct_request_true_reply_prefix_query` identifies its direct-service query
with the previously computed `vn_fair` measure, and
`von_neumann_request_true_reply_probability_half` transports it to the
unbounded implementation.  The existing expectation theorem therefore reads
its true mass as `1/2`.
`von_neumann_request_true_reply_trace_probability` packages the same result
as the paper-facing statement
`Prₜ[von_neumann_service | request_true_reply_trace] = 1/2`.
`direct_request_true_reply_sem_coupled_to_fair` connects the canonical
function to the explicit fair witness, while
`von_neumann_request_true_reply_sem_preserved` states preservation directly
between the two canonical denotations.  `direct_reply_first_prefix_rejected` checks a
non-matching first event.  Separately,
`canonical_spin_nonempty_trace_query_zero` proves that pure silent divergence
produces a zero-mass nonempty trace query, and
`divergent_trace_query_not_rejection_mass` distinguishes that missing mass
from an ordinary mass-one `false` result.

This is finite prefix-satisfaction/cylinder semantics, not a distribution on
traces.  The maintained theory does not claim a probability measure on
infinite traces or a general WP calculus.

The artifact support range is Coq `>= 8.20` and `< 9.0`, with CI explicitly
installing Coq 8.20.1.  Coq 9 changes Stdlib load paths and requires a
separate migration; it is not part of the current compatibility claim.

## Finite internal compression

The public definition is now in `Eq/PFinite.v`.  There is no parallel
candidate relation, stable-hitting premise, fuel index, or omega interface
in its definition.

`finite_internal t out` is inductive.  FIStop returns the current residual
tree, FITau consumes one silent node, and FIProb integrates the residual
distributions of its branches.  A derivation is well-founded: every branch
must finish its selected compression, but infinitely many branches may
have no common finite depth bound.  The residual tree need not terminate,
be stable, or be almost-surely terminating.

`pfinite_guard RR sim` matches the two observed residual constructors using
`pstrongF RR sim`.  Only their continuations recurse.  The generator
`pfiniteF RR sim` chooses two finite_internal derivations and couples their
outputs with this guard.  Its greatest fixed point is `pfinite_rel RR`.
The homogeneous `pfinite` is its finite reflexive-symmetric-transitive
closure.  `pfinite_refl`, `pfinite_sym`, `pfinite_trans` and
`pfinite_equivalence` are proved; no transitivity of the raw heterogeneous
GFP is assumed.

The structural inclusions are backend-generic.  `pfinite_rel_tau_prefix`
and `pfinite_prob_tau_prefix` remove selected administrative Tau prefixes,
including prefixes under a Prob node.  This is a finite-compression law,
not a generic congruence axiom for arbitrary branchwise pfinite proofs.
`ResidualFinite.v` checks nonuniform branch depths and rejects
silent divergence versus return.

### Behavioral soundness and the capability boundary

`Eq/FreeOmega/FiniteInternalTransport.v` proves the generic implications

~~~text
sim ⊆ pfiniteF RR sim  ->  sim ⊆ peutt RR
pfinite_rel RR         ⊆   peutt RR
pfinite               ⊆   peutt eq
~~~

The endpoints are `peutt_coinduction_residual`, `peutt_of_pfinite_rel`
and `peutt_of_pfinite`.  They use the maintained core, Dirac-AE,
bind-AE-exactness, coupling-AE and countable-AE capabilities, plus the
explicit optional `FreeOmegaNativeCouplingLaws`.  This last capability
realizes a quotient coupling of two native presentations as an actual
joint on their original sample carriers.  It mentions neither trees,
stable hitting nor behavioral equivalence, and also implies ordinary
node-lifting realization via identity decoders.

This extra capability is PROVED for SubEnum, by
`SubEnum_FreeOmegaNativeCouplingLaws`; importing
`FreeOmegaNativeCouplingSubEnum` makes the instance available.  The generic
facade does not import concrete backend instances.  No instance is claimed for raw
Enum or MathComp.  Consequently the NEW finite relation's behavioral
inclusion is conditional for those backends.  This is an explicit change
from the old finite-stable-prefix API, not an assertion that core measure
laws alone now imply the stronger result.  The shared behavioral backend
profile remains unchanged; this optional proof-relation capability is
audited separately in `BackendCapabilities.v`.

Ordinary native witness recovery is now proved for MathComp as
`mathcomp_coupling_realization` in `SemanticCouplingMathComp.v`, without
`MathCompCouplingGluing`.  It pushes the backend's existing joint on
`mc_joint A B` into a kernel on `mc_carrier (A * B)`, preserving both graph
marginals and the AE relation.  One-sided bookkeeping bottoms are null
under a valid coupling; no normalization or default returned value is
introduced.  The foundational audit includes an empty-carrier regression.
This removes the native repackaging obligation, NOT the stronger
quotient-to-native reflection obligation above; in particular it does not
yet provide `FreeOmegaNativeCouplingLaws` for MathComp.

For raw Enum, the remaining reflection proof cannot reuse SubEnum's
unit-interval bounds: arbitrary intermediate weighted terms can have
infinite upper mass.  The internal audit in
`FreeOmegaUpperExpectationEnum.v`, `FreeOmegaUpperCouplingEnum.v`,
`FreeOmegaUpperContinuityEnum.v`, and `FreeOmegaUpperObservationEnum.v`
now interprets such terms in extended nonnegative reals.  It proves native
coupling comparison, AE extensionality, monotone convergence (including
AE-only monotonicity at sample nodes), and consistency of the complete
`free_omega_observes` judgment, including its raw-increasing Lub rule.
It reuses the existing rational-to-real finite-atomic limit lemmas rather
than adding a measure-consistency axiom.  `ExtendedEnum.v` checks mass two,
zero times infinity, null-entry continuity, and a raw-increasing chain with
upper mass +infinity that admits no finite native observation.
Preservation by ALL quotient-coupling constructors is still to be proved;
these scalar results alone do not yet justify an Enum instance of
`FreeOmegaNativeCouplingLaws` or unconditional Enum `pfinite` soundness.
The evaluator is a proof-internal upper functional, not a new public
probability API or a claim that arbitrary formal Lub syntax is additive.

The soundness proof does not assume equivalence of the recursive candidate,
AST, total mass, a uniform fuel bound, a chosen joint from each client, or
that the candidate is already behaviorally sound.  It extracts a native
joint for each compression pair, extends it through the strong guard, and
uses the library's correlated, separately costed recurring-process theorem
`peutt_coinduction_joint_rows`.  Finite equational chaining is handled by
ordinary induction AFTER raw-GFP soundness, not by an up-to-equivalence rule.

### Proved SubEnum realization

The construction in `FreeOmegaNativeTransportSubEnum.v` covers arbitrary
heterogeneous relations and noninjective, higher-universe decoders:

1. `FiniteEnumPresentation.v` represents native enumerations by ordinal
   positions.  Decoding exactly recovers the original list, retaining
   duplicates and zero weights; empty carriers need no default element.
2. Conditional recovery pulls quotient couplings back to these finite
   positions without replacing a random sample by a selected partner.
3. `FreeOmegaUpperQuotientSubEnum.v` proves bounded-test comparison for
   ALL quotient constructors, including observation, composition,
   AE restriction and continuous limit rules.  Indicator tests yield Hall
   inequalities; constant tests yield equal total mass.
4. `FiniteMatching.v`, `FiniteCapacityMatching.v` and
   `FiniteRationalTransport.v` construct a rational transportation matrix
   from those inequalities.  The matching/capacity/transport existence
   theorems are closed under the global context.
5. `FiniteEnumTransport.v` realizes that matrix as an actual enumeration
   with exact marginals, then transports the joint back to the original
   carriers.

The scalar model is an internal audit of formal FreeOmega terms, not a
second public probability backend or a claim that arbitrary non-increasing
Lub terms define additive measures.  Its abstract realType is instantiated
internally with Coq's standard real construction via
`coq-mathcomp-reals-stdlib`.  Assumption inspection records the inherited
classical/extensionality/dependent-equality principles and the standard
real dependencies `ClassicalDedekindReals.sig_not_dec` and
`ClassicalDedekindReals.sig_forall_dec`.  No reflection, gluing or soundness
axiom was added for SubEnum.

### Regressions and rejected shortcuts

`ResidualTransport.v` proves that its three-pair retry candidate is not
reflexive, embeds it into the raw pfinite GFP by coinduction, and promotes
that result to peutt.  It also checks heterogeneous result relations.
`ResidualJointCoinduction.v` uses the generic rule for unbounded retry
with discarded random bits, an eventful success continuation, and an
always-failing instance.  `NativeRecovery.v` checks automatic round
extraction even with the constantly false continuation candidate.

`FiniteTransport.v` forces one source atom to split across two targets,
checks zero mass and empty carriers, and rejects identity transport between
unequal marginals with the same support.  Scalar-model regressions reject
mass collapse and preserve the RandomWalk limit's mass.

The negative audits remain important.  `ResidualClosureAudit.v` refutes
`sim ⊆ pfiniteF (equivalence_closure sim)` as a sound general rule,
including for reflexive/symmetric candidates: spin can then be falsely
related to a return.  `NativeReflection.v` supplies a backend showing
that quotient-to-native reflection does not follow from the generic core
laws alone.  These are reasons to keep the new capability explicit, not
counterexamples to the proved SubEnum theorem.

The earlier policy-only, reference-coupling and equivalence-class coding
lemmas remain internal proof infrastructure where independently useful.
Obsolete public relation definitions and the superseded
equivalence-only/concrete-only coinduction wrappers have been removed.

## Infinite-state random walk

`Examples/RandomWalk.v` encodes the while loop on `(height, streak)` with
down/reset probabilities `2/3` and `1/3`, using the intrinsic `SubEnum`
node carrier and `FreeOmega SubEnum` behavior.

The proof has two explicitly distinguished layers:

- `run_split` is a carrier-independent `pstruct` theorem factoring a descent
  of `a+b` levels into a descent of `a` levels followed by `b` levels.
  It now instantiates the library theorem `pstruct_iter_split_at`; there is
  no example-local coinductive candidate.  The library law relates a source
  loop to a prefix loop: before the barrier, the bodies agree structurally
  and only retry; at the barrier, the prefix returns the source's resumption
  state without an additional Tau.  Neither probability laws nor eventual
  arrival at the barrier are assumed.  The hierarchy regressions also test
  visible interactions and an unreachable barrier.
  `height_two_split` identifies the reset branch with `D_0 >>= passage`.
  `random_walk_passage_normal_form` and `passage_unfold` promote structural
  control-flow reasoning to actual `peutt` equations.
- `walk_harmonic_error` proves the uniform-in-streak error bound
  `|(finite evaluation) - H(x,y)| <= (3/2)^x (17/18)^rounds` for every
  bounded harmonic candidate with the stated boundary values.
  The constant-one candidate proves AST; an explicit candidate gives each
  output atom.  This is an elementary rational convergence argument, not an
  imported random-walk theorem or an assumed uniqueness of fixed points.

`walk_hitting_observes` and `joint_hitting_observes` connect these calculations
to the existing primitive stable-hitting approximants.  A complete round
consumes two internal steps (`Prob`, then the `Tau` introduced by `iter`);
`walk_schedule_ge` and cofinality justify taking that subsequence of fuels.
`random_walk_ast` is consequently the maintained `ptree_stable_hitting_ast`
predicate for the original source tree, not a separate numerical definition
of AST.

`random_walk_outputs_spec` identifies the source's finite joint observations.
`random_walk_output_dist` proves their pointwise limits are `joint_pmf`:
`joint_pmf (0,S n) = (2/3)(1/3)^n`, and zero for all other states.
`joint_pmf_normalized` proves the finite sums converge to one.
`random_walk_closed_form` packages these statements with native AST.
`continuation_pmf` and `D0_geometric_equation` also verify the successor-tail
and geometric renewal formulas for the proved limiting probabilities.
`continuation_stable_hitting_ast` transports the two-level limit through
`height_two_split` to the actual bind program in the renewal equation.
The regression for output `(0,2)` gives mass `4/27` after three rounds but
limiting mass `2/9`, distinguishing finite execution from the unbounded law.

The assumption audit reports `run_split` and `walk_harmonic_error` closed
under the global context, as is the new `pstruct_iter_split_at` library law.
`random_walk_closed_form` uses the existing
functional-extensionality and dependent-equality axioms; `passage_unfold`
additionally inherits the generic behavioral theory's choice principles.
No example-specific probability axiom or unfinished proof is introduced.

`walk_approx` is now the identity specialization of `walk_observation`,
rather than a duplicate recursive execution function.  Its expectation law
specializes `walk_observation_expect`.  The scalar fold `walk_eval` remains
useful for the harmonic induction and executable regressions; both folds
are certified against primitive execution by `walk_hitting_observes`.

The renewal proof now stays in the finite layer.
`passage_unfold_guarded` supplies the structural equation; promotion to
pfinite followed by `pfinite_prob_tau_prefix` removes one Tau in each
coin branch.  The result is `passage_unfold_finite`, with no stable-hitting
or AST premise.  `passage_unfold` is then a direct application of the
SubEnum behavioral subrelation.
Assumption inspection of `passage_unfold_finite` reports only
`Eqdep.Eq_rect_eq.eq_rect_eq`; the finite equation itself does not use
the real-model assumptions needed by its behavioral promotion.

The generic `peutt_prob_rewrite` remains useful for arbitrary local
relations registered below peutt, including coupled different sample types.
The hierarchy tests cover that contextual rule, bind/fmap promotion, and
the stronger finite administrative Prob/Tau law with a divergent branch.
No arbitrary eventful iter congruence or new general Prob congruence is
asserted for pfinite.
The quantitative proof uses a bounded harmonic candidate instead of the
proposal's scalar equation `m = p + q*m*m`: the former constructs the
required limits directly without first requiring a real-valued mass for an
arbitrary FreeOmega expression.  In particular, no scalar cancellation rule
is assumed for `peutt`.  The normalized countable law is expressed by limits
of primitive finite observations, **not** as an element of finite `SubEnum`.
A theorem equating the source to a geometric sampler under `peutt` remains
outside this endpoint; pointwise PMF equality is not silently promoted to
behavioral equivalence.

## Exact no-Prob / ITree boundary

The maintained generic theorem deliberately does **not** claim

```text
peutt eq (embed t) (embed u) <-> eutt t u
```

under the current `SemanticMeasure`.  The converse is not derivable
from these axioms and is false for admissible degenerate instances: the
interface gives positive coupling constructors and algebraic closure laws,
but it does not require couplings to separate unequal Dirac measures, reflect
zero mass, or invert a coupling of stable heads.  An implementation whose
`sem_lift` relates every pair satisfies the basic positive laws and makes
`peutt` universal, while ITree `eutt` is not universal.

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
