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

`Examples/FreeOmegaLimitSafety.v` records the rejected decreasing-mass and
moving-diagonal inputs.  The former uses a valid mass-one coin and compares
mass one with mass two thirds, so this is not a raw-weight validity issue.
These tests repair the identified rule-boundary vulnerabilities; they are
**not** a claim of a complete mass-preserving denotational soundness theorem
for every FreeOmega quotient constructor.  That stronger theorem remains
unproved.  The unrestricted residual `pfinite` soundness result below also
remains open; unary-policy acceleration is not silently generalized to it.

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
The heterogeneous `pfinite_rel` adds an inductively finite one-sided Tau
closure and finite-complete stable-prefix collapse; the inductive closure is
intentionally outside the greatest fixed point, so an infinite one-sided Tau
loop cannot justify an arbitrary relation.  The public homogeneous `pfinite`
is its finite reflexive-symmetric-transitive closure.  Consequently
`pfinite_refl`, `pfinite_sym`, `pfinite_trans`, and
`pfinite_equivalence` are available without introducing any omega execution
rule.  `Eq/FreeOmega/Relation.v` proves soundness first for `pfinite_rel` and
then for the whole equivalence closure.  The adjacent
inclusions are registered with Rocq's `subrelation`.  `PEutt.v`
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

## Residual finite-compression redesign (in progress)

The proposed replacement for `pfinite` is implemented separately in
`Eq/PFiniteResidual.v`, and is **not yet the public `pfinite` relation**.
The current `PFinite.v`, its soundness theorem, and the public facade are
unchanged until greatest-fixed-point soundness of the replacement is proved.
The temporary candidate names are migration scaffolding, not a second
intended public behavioral relation.

`Eq/FiniteInternal.v` defines the inductive operational judgment
`finite_internal t out`, with `FIStop`, `FITau`, and `FIProb`.  It returns a
distribution of residual trees, not stable heads.  There is no fuel or
stable-hitting condition.  Infinitely many sampling branches may have
different finite depths with no uniform bound; the derivation is
well-founded, not necessarily a finite tree.

The candidate generator couples these residual distributions under
`pfinite_guard RR sim`, a single `pstrongF` match whose continuations use
`sim`.  Thus `FIStop` cannot make an unguarded recursive proof valid.  The
candidate has proved `pstrong` inclusion, heterogeneous converse, return
relation monotonicity, and reflexivity.  As in the current API, its
homogeneous equivalence is the finite reflexive-symmetric-transitive closure;
this does not assert transitivity of the raw heterogeneous greatest fixed
point.

The completed semantic results in `Eq/FiniteInternalHitting.v` are:

- `finite_internal_hitting_lift`: the original complete hitting behavior
  couples by equality to the bind of the residual distribution with its
  complete hitting behaviors.  The conclusion is a coupling, not an
  unjustified equality or closure of a chosen limit representative.
- `peutt_of_finite_internal`: coupling residuals by **already proved**
  `peutt` is a sound behavioral rewrite.
- `pfinite_residual_round_sound`: one candidate round with `peutt` as its
  recursive relation is sound, including heterogeneous return relations.
- `finite_internal_match` and `finite_internal_closure_compatible`: finite
  compression preserves native generator matching for arbitrary continuation
  candidates.  Thus `peutt_coinduction_upto_finite_internal` is a proved
  compatible-closure rule, rather than an appeal to a final congruence inside
  its own coinductive proof.  Its progress premise is still a complete
  stable-hitting match, not merely a `pstrongF` internal guard.
- `FreeOmega/FiniteInternal.v::finite_internal_hitting_covered`: every
  primitive n-step observation is below the result of first performing any
  well-founded compression and then running each residual for n steps.
  The index is a proof-level semantic approximation; it imposes no uniform
  depth bound on `finite_internal`.
- `finite_internal_rounds_cover_hitting`: for any independently selected
  valid compression policy, n+1 compression/guard rounds cover every
  observation reached within n primitive internal steps.  The accelerated
  approximants are increasing (`finite_internal_rounds_increasing`).
  This establishes lower coverage through arbitrarily many internal rounds,
  not just preservation of a single compression.
- `finite_internal_round_limits_coupled`: if two independently selected
  policies couple their residuals under `pfinite_guard RR sim` at every
  related state pair, their complete accelerated chains are coupled under
  `stable_head_rel RR sim`.  This is a coupling of actual omega chains;
  no assumed inclusion in `peutt` occurs in its proof.
- `finite_internal_approximation_exists`: every well-founded cut has an
  increasing chain of uniform-depth truncations converging to its residual
  distribution.  The truncations have both primitive-fuel upper bounds and
  lower coverage.  This does not put a uniform bound on the original cut.

`Eq/FreeOmega/FiniteInternalAcceleration.v` completes the acceleration
adequacy argument for any selected compression policy:

- `finite_internal_grid_cofinal` proves that primitive hitting and the
  diagonal of the truncated-round grid are mutually cofinal.
- `finite_internal_acceleration` couples the complete accelerated limit
  by equality to the original primitive hitting limit.  The scheduling grid
  is constructed from the well-founded derivations; it is not an extra
  hypothesis, and branch depths need not have a uniform bound.
- `peutt_coinduction_finite_internal_policies` is therefore a proved native
  coinduction rule for two valid marginal policies with guarded residual
  coupling.  Unlike `peutt_coinduction_upto_finite_internal`, its premise
  needs only `pstrongF` matching after compression.  It handles indefinitely
  repeated internal Tau/Prob rounds with no intervening visible event.

The round-soundness lemma establishes `F(peutt) ⊆ peutt`, **not**
`νF ⊆ peutt`.  Greatest-fixed-point soundness still needs to connect its
pair-dependent compression witnesses to the proved unbounded execution
argument.  The old proof, which recurs only after stable observations,
does not supply this connection.  No additional capability axiom, intersection
with `peutt`, or unfinished proof has been used to disguise this gap.

The unary-policy acceleration limit obligation is solved.  The remaining gap to the
unrestricted residual GFP is witness dependency: the existential
compression witnesses in `pfinite_residual_unfold` may
depend on the whole related pair.  Classical choice on pairs does **not**
produce the independent marginal policies assumed by
`peutt_coinduction_finite_internal_policies`.  A proof must handle this dependency,
not silently strengthen the generator to require such policies.  Neither
uniformization nor unrestricted GFP soundness is currently claimed solved;
no new capability axiom replaces this obligation.

`Prob/SemanticCoupling.v` and `Eq/FiniteInternalJoint.v` begin the
pair-dependent execution bridge, without assuming independent policies:

- `semantic_coupling` records an **explicit joint measure**, its two graph
  couplings to the marginals, and AE support in the candidate relation.  It
  is a certificate, not a new typeclass axiom.  `semantic_coupling_sound`
  recovers ordinary `sem_lift` from the certificate; the converse is **not**
  assumed or claimed proved for arbitrary FreeOmega quotient couplings.
- `semantic_coupling_dependent_bind` permits continuations to depend on the
  entire sampled pair.  Its left/right marginal lemmas and
  `semantic_coupling_bind_dependent` preserve the joint's probabilities and
  compose concrete next-joint certificates, including off-support branches.
- `pfinite_residual_paired_cuts` applies classical choice at the correct
  domain: pairs of related trees.  It extracts valid paired cut functions
  from any post-fixed candidate without a uniformization hypothesis.
- `finite_internal_joint_guarded` couples the resulting marginal residual
  distributions.  `finite_internal_joint_hitting_left/right` prove that
  completing those residuals preserves each original marginal's hitting
  behavior.  These are finite-round results, not yet the GFP soundness
  theorem or an infinite-history acceleration theorem.

`Examples/PairedFiniteCompression.v` checks a correlated stopping choice:
the same left tree `Tau (Tau (Ret true))` is cut by two steps or one step
according to its right partner.  The resulting left residual distribution
mixes `Ret true` and `Tau (Ret true)` with positive weights.  It is proved
not equality-coupled to **any** unary finite-internal cut of that left tree,
yet the joint-compression theorem preserves its complete hitting behavior.
This rules out replacing the chosen paired strategy by a unary cut merely
by changing its measure representation.  It does not claim that the program
pair admits no other useful unary policy.

To complete this joint-execution route, one must account for joint witnesses
of arbitrary residual couplings and for acceleration adequacy of infinitely
many correlated guard rounds.  The certificate API and finite-round
preservation lemmas alone do not discharge those obligations.

Joint-witness extraction now has concrete proved cases:

- `Prob/SemanticCouplingEnum.v::enum_coupling_realization` recovers a joint
  enumeration from the backend's position-indexed coupling.  The public
  theorem permits arbitrary value types, including functions; classical
  equality is local to the conversion proof, not a client `eqType` premise.
  `subenum_coupling_realization` additionally proves the joint's mass is that
  of its marginal and therefore packages it within the native SubEnum bound.
- `Prob/FreeOmegaCoupling.v::free_omega_lift_realization` constructs joint
  FreeOmega measures by induction over the **structural** lifting, including
  its `Lub` constructor, from a node witness-extraction theorem.  Concrete
  Enum and SubEnum corollaries in `FreeOmegaCouplingEnum.v` discharge that
  premise; they do not register an unproved capability class.
  The `Lub` case provides graph marginals and AE support, but does **not**
  assert that independently selected row joints form an increasing chain.
  A later infinite-history argument must establish monotonicity separately
  wherever it uses cofinality or diagonalization.
- `semantic_coupling_transport` preserves an explicit joint under equality
  lifting of both marginals, without equality reflection.  Consequently
  `free_omega_lift_realization_mod_eq` realizes general many-to-many
  structural couplings after quotient-equality rewrites on either side.
  It does not assume that every relational quotient coupling can be put
  in this form.
- `free_omega_qlift_graph_realization` handles the **full quotient lifting**
  for function-graph relations.  Its equality specialization constructs a
  diagonal joint without disintegration or a new backend assumption.
  Consequently `finite_internal_acceleration_joint` realizes the complete
  acceleration equality, including its cofinal/diagonal limit proof, as an
  explicit joint certificate.  This result is not restricted to bounded
  cuts or bounded numbers of guard rounds.

`Examples/CouplingRealization.v` checks function-valued node carriers,
structural `Lub` witnesses, relational marginal rewrites, and a quotient
equality that provably has no structural lifting derivation.
`PairedFiniteCompression.v` now also extracts
its residual joint from the structural coupling proof instead of requiring
the example's hand-written joint.

The extraction gap is therefore narrower but not closed: arbitrary
relational `free_omega_qlift` witnesses are still not realized by these
theorems.  Neither the structural theorem nor the graph theorem is silently
applied to general many-to-many guard relations.  The unrestricted residual
GFP soundness theorem remains unproved, and the public `PFinite` API is not
replaced on the strength of these partial realization results.

`Eq/FreeOmega/FiniteInternalJoint.v` now constructs actual paired execution:

- `finite_internal_guard_joint_exists` realizes one `pstrongF` guard using
  only a node coupling realizer.  Ret/Vis produce related paired heads;
  Tau/Prob produce paired residual trees.  Enum and SubEnum discharge the
  node premise with proved theorems, not new capability axioms.
- `finite_internal_paired_kernel_exists` chooses residual and guard joints
  on **pairs**, then composes them into a fixed joint kernel.  It proves
  both graph marginals equal the corresponding cut-followed-by-guard
  transitions and proves AE closure of residual/head relations.  It still
  explicitly requires realizability of each residual coupling.
- `finite_internal_paired_rounds_increasing` and
  `finite_internal_paired_hitting_coupled` establish increasing joint-round
  approximants, head support at the complete hitting limit, and a coupling
  of that limit's two projections.  The chain is obtained by executing one
  fixed kernel, not by independently choosing a coupling at each fuel.

`Eq/FreeOmega/FiniteInternalJointHitting.v` additionally proves
`finite_internal_realized_round_hitting`: resolving a realized round's
stable outputs immediately and completing its residuals with their original
hitting distributions recovers the source tree's complete hitting up to
equality lifting.  This uses validity of the finite cut and the round's
graph marginal, and is therefore probability preservation rather than only
support preservation.  It is a one-round completion equation, not yet a
proof that an infinite sequence of uncompleted rounds is adequate.

`Examples/CorrelatedInternalRounds.v` instantiates the construction with the
partner-dependent cuts from `PairedFiniteCompression` and with the purely
internal, unbounded retry loops from `ResidualFinite`.  The latter's existing
cut proof now exposes its structural lifting before promotion to the quotient
lifting, so the residual joint can be extracted automatically.  A negative
regression rules out an always-zero kernel as a round certificate for the
returning pair: AE closure alone would permit it, but the graph-marginal
obligations do not.

The correlated example also checks the completion equation for each of the
two original marginals; neither proof substitutes an independent policy.

`Eq/FreeOmega/KernelCompletion.v` proves the upper-bound direction of
infinite execution using completion of finite prefixes:

- `kernel_completion_eq` propagates a one-round completion equation to
  every finite number of rounds, on an AE-closed domain of states.
- `kernel_hitting_approx_below_completion` gives a **raw** approximation
  bound from actual truncated hitting to the corresponding completed
  prefix.  Unresolved mass is zero on the former side.
- `kernel_hitting_limit_upper` constructs an explicit `upper` with raw
  approximation from the complete projected hitting to `upper`, and an
  equality coupling from `upper` to the proposed full behavior.  It does
  not transport the raw order across that equality.  Its formal completion
  limit is related to a constant chain by pointwise equality; no claim of
  raw monotonicity, or use of cofinality, is made for that completion chain.
- `FiniteInternalJointHitting.v::finite_internal_execution_hitting_upper`
  discharges the completion equation using **valid finite cuts** and the
  actual graph marginal of a realized round.  States may contain both
  trees or richer history: cuts need not factor through the projected tree.
  The correlated-cut and internal-retry regressions both instantiate this
  complete-hitting upper bound against their original tree semantics.

`Examples/KernelCompletion.v` guards against mistaking this upper half for
adequacy: a pure internal self-loop admits a returning tail that satisfies
the completion equation, and has an upper bound of the above form, but its
actual hitting is zero and is **not** equality-coupled to that returning
tail.  A fixed-point equation alone does not identify the least solution.
A second regression exhibits a two-stage terminating kernel with a valid
completion equation but a non-raw-increasing completion sequence, ruling out
the shortcut of applying monotone cofinality to such sequences without proof.

These paired-round results are still **not full** correlated acceleration
adequacy.  The reverse coverage argument must use actual progress through
primitive steps in each valid cut-and-guard round.  The projected limits
have not yet been proved equal to the original trees' complete hitting.
That identification and unrestricted residual realizability remain
necessary for the residual GFP soundness theorem.

`Examples/ResidualFinite.v` checks nonuniform branch depths, local Tau removal
before divergence, Prob branch compression, and the negative core regression
`residual_finite_spin_not_ret`.  `residual_services_peutt` checks the sound
up-to-compression rule on infinitely interacting services with different
finite delays on every continuation.  It also derives the actual RandomWalk renewal
equation as `random_walk_passage_residual_finite`, without behavioral Prob
congruence.  That example is a client of the candidate, not a replacement for
the maintained `passage_unfold` until the soundness bridge is complete.
`residual_retries_peutt` checks the stronger policy-based rule on purely
internal retry loops, with one Tau per failed toss on one side and two on
the other.  There is no Vis guard between retries and the proof does not
first assume a behavioral equivalence for the recursive continuations.

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

The renewal proof now uses local finite rewriting with a behavioral
contextual conclusion.  `passage_unfold_guarded` first promotes from
`pstruct` through `pfinite` to `peutt`.  Each branch removes one Tau using
`pfinite_tau_l`, and `peutt_prob_rewrite` promotes these branchwise proofs
under the probability node.  The result is `passage_unfold : peutt ...`,
not a claimed `passage_unfold_finite` equation.  No Prob congruence has been
added to `pfinite`: local finite rewrites need only remain behaviorally sound
when placed under a context, not globally finite.

`peutt_prob_rewrite` is backend-neutral and accepts any registered
subrelation of homogeneous `peutt`; it also accepts a coupling between
different sample types/measures.  The hierarchy regressions cover same-measure
and coupled sampling, a divergent continuation, and promotion under the
existing bind/fmap Proper instances.  Direct branchwise `setoid_rewrite`
under `Prob` currently unfolds the constructor to `go/ProbF` and fails to
find the needed morphisms; explicit contextual promotion avoids adding a
new typeclass search graph.  This does not claim arbitrary eventful iter
congruence: the existing eventless behavioral theorem and eventful
generator-closure obligation retain their documented scope.

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
