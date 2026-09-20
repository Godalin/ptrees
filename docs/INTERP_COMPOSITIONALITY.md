# Interpretation: staged compositionality work

Each stage stops for review before the next one starts. No new equivalence,
transition semantics, heterogeneous-effect framework, or general StateT
library is part of this work.

| Stage | Deliverable | Status |
| --- | --- | --- |
| 1. InterpExposure | Decide whether arbitrary interpretation preserves `tree_trans_bisim` | Accepted baseline `4703035` |
| 2. GuardedInterp | Semantic visible guarding, then `interp_vis_fusion` and peutt preservation | Accepted baseline `268a223` |
| 3. AtomicInterp | A sufficient atomic-handler contract for transition preservation | Accepted baseline `8e09561` |
| 4. MDPInterp | An explicit handler contract preserving `mdp_state` | `98b93aa` core/API accepted; independent-source regression fix awaiting final review |
| 5. StateInterp | Focused StateT interpreter, algebra, and rewrite-oriented example | Not started |
| 6. General interp | Revisit arbitrary-handler peutt preservation without making it a blocker | Deferred |

## Stage 1: a two-round handler exposes the hidden correlation

The checked experiment is
`Regression/Semantics/InterpExposure.v`. It imports the existing strictness
witness rather than duplicating its programs or its source-bisimulation proof.
It belongs with the comparison regressions; no library or paper-facing case
study acquires a dependency on regression fixtures.

The native/behavior pair is `SubEnum / FreeOmega SubEnum`. On the single
event interface `Query : correlationE bool`, the source programs are:

```text
P = sample b ~ fair; Query x; return b
Q = sample b ~ fair; Query x; return (if x then not b else b)
```

The accepted source theorem is `tree_trans_bisim P Q`. For a false response
its coupling matches the same hidden bits; for a true response it matches
opposite bits. The couplings may depend on the response.

The new handler is deterministic and has two finite visible interactions:

```text
two_query_handler Query = Query ignored; Query x; return x
```

Both source and target use **the same** event interface. This is ordinary
`PTree.interp`, including its existing administrative Tau, not a custom
interpreter. `two_query_handler_first_hitting` proves that the handler's
complete first behavior is a Dirac measure at a visible head.

After interpretation the programs behave as:

```text
interp h P = sample b ~ fair; Query ignored; Query x; return b
interp h Q = sample c ~ fair; Query ignored; Query x;
             return (if x then not c else c)
```

These displays suppress only the interpreter's administrative Tau. The
formal witnesses in `exposure_hitting` retain the actual interpreted trees.
`exposure_returns` and `exposure_offers` prove the same current observation
measures for both sides, so neither returns nor offered labels cause the
separation.

`exposure_first_transition` computes the first action's **weighted**
successor distribution: a fair mixture of the second `Query` heads. There
is no filtering/conditioning normalization. The first answer is ignored,
so either first response produces that same distribution.

Now transition bisimulation must couple these successor states. Every
supported pair, with hidden bits `b,c`, must itself be bisimilar at the
second `Query`. Its two possible responses force respectively:

```text
x = false: b = c
x = true:  b = not c
```

No pair works. `exposure_second_pair_impossible` proves this from the
transition and return-observation endpoints. Coupling support transport
then rules out **every** coupling of the first successor measures, not only
the diagonal coupling. No peutt-negative theorem is used for this direction.

The checked regression endpoints are:

```coq
tree_trans_bisim_interp_counterexample :
  TB P Q /\ ~ TB (PTree.interp two_query_handler P)
                   (PTree.interp two_query_handler Q).

tree_trans_bisim_not_interp_congruent :
  ~ (forall handler t u, TB t u ->
       TB (PTree.interp handler t) (PTree.interp handler u)).
```

Here `TB` is the existing canonical-backend `tree_trans_bisim eq`, not a
new relation.

## What this does and does not establish

- Arbitrary effectful interpretation does **not** preserve this
  response-wise transition bisimulation, even on this finite example.
- Merely exposing a target Vis before returning is not sufficient for
  transition preservation: this handler already does so. This motivates
  investigating a stronger atomicity condition in stage 3; it does not
  establish that a particular atomicity definition is necessary or sufficient.
- The witness does not refute peutt preservation: the source pair is already
  known **not** to be peutt-equivalent. General peutt preservation remains
  conditional on `interp_vis_fusion`; stage 2 below now discharges it under
  semantic visible guarding.
- This is a bisimulation (rather than linear-trace) obstruction. It does not mean one run
  queries the source continuation twice, nor does this proof claim a
  distinguishing linear finite-interaction probability.

## Validation

At stage 1, the full build passed, including the new module in `AllImports`,
whose inventory guard then covered all 191 other modules. Its endpoints inherit exactly
functional extensionality and `Eqdep.Eq_rect_eq.eq_rect_eq` in their
`Print Assumptions` audits; no new axiom, choice premise or unfinished proof
is introduced.

The targeted kernel check passed: it loads the full-library universe context
and rechecks the new module and the import harness together:

```sh
python3 tools/check_aggregate.py
opam exec -- dune build
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Regression.Infrastructure.AllImports \
  -norec PTree.Regression.Semantics.InterpExposure
```

This is a targeted joint kernel audit, not a claim that every existing
proof in the repository has been independently rechecked this round.

## Stage 2: semantic guarded interpretation

`Eq/FreeOmega/GuardedInterp.v`, exported by `Eq/FreeOmega.v`, supplies the
new sufficient condition without changing `interp_vis_fusion`, `interp`,
peutt, or either transition semantics.

For each source event `e : E X`, the condition is:

```text
guarded_handler h :=
  for every complete hitting witness mu of h(e),
    AE mu (fun head => head is FHVis, not FHRet).
```

`stable_head_is_visible` is `False` on Ret heads and `True` on Vis heads.
This is an almost-everywhere statement about complete behavior. There is
no syntactic-shape restriction, finite-fuel bound, totality, or AST premise.
Arbitrary internal Tau/Prob prefixes and missing mass are allowed. Complete
divergence has empty support and is allowed too. A zero-mass return branch
is harmless; a reachable direct return violates the condition.

Complete hitting exists in the FreeOmega backend, so the universal
witness quantification is not vacuous. `guarded_handler_of_hitting` lets
clients prove the condition with one convenient complete witness for each
event; uniqueness and coupling support transport then cover every witness.

### Proof structure and endpoints

```text
guarded_handler
  -> guarded_handler_vis_fusion
  -> existing peutt_interp_of_vis_fusion
  -> peutt_interp_guarded
  -> peutt_interp_guarded_Proper
```

For related source continuations, the fusion proof obtains the handler's
complete head measure and uses the existing stable-hitting bind theorem
on each side. It restricts the diagonal coupling to the handler's AE-visible
support. Thus its only surviving case is a Vis head. At this fresh visible
guard, the residual handler continuation is related to itself by peutt,
while its return continuations re-enter the interpreted-source candidate.
That is exactly the already-proved `bind_upto_closure`. No recursive use of
the theorem being proved is hidden in a side condition.

The endpoint supports arbitrary heterogeneous return relations:

```text
guarded_handler h -> peutt RR t u -> peutt RR (interp h t) (interp h u).
```

It uses the existing FreeOmega capability context: native `SemanticMeasure`,
Core, AE-lifting, Coupling-AE and Countable-AE laws, and `SemanticOmega`.
No new backend class or measure axiom is introduced. The theorem retains
the existing `E -> F` interpreter parameters, without developing a new
effect-signature framework; all new program regressions use `E = F`.

`peutt_interp_guarded_Proper` is an explicit proof-producing endpoint.
Clients register its result locally after proving guardedness; the library
does not add a global instance that asks typeclass search to invent such a
proof for an arbitrary handler. The regression uses actual `setoid_rewrite`.

### Checked boundaries

`Regression/Semantics/GuardedInterp.v` checks:

- The very same `two_query_handler` from stage 1 satisfies the condition
  and preserves peutt. `two_query_compositionality_contrast` packages this
  together with its independently proved transition counterexample.
- A fair internal sample choosing between a delayed visible protocol and
  silent divergence is guarded and preserves peutt: neither immediate
  visibility nor termination is required.
- Sampling from a Dirac `true` with a syntactically present `false -> Ret`
  branch is guarded. Replacing AE guarding by pointwise branch guarding
  would wrongly reject this example.
- An immediately returning handler is not guarded. This is a boundary of
  the sufficient condition, not a negative preservation theorem for all
  unguarded handlers.
- Local Proper/setoid rewriting works, and preservation supports a
  non-equality relation between Boolean and natural-number returns.

This guarded result alone does not strengthen the known false transition
congruence claim or establish arbitrary-handler peutt preservation. Stage 3
below uses a strictly stronger, explicitly delimited handler contract.

### Stage 2 assumptions and validation

`guarded_handler_of_hitting` inherits `eq_rect_eq`. The fusion, preservation
and Proper endpoints inherit the existing functional extensionality,
`eq_rect_eq`, `RelationalChoice.relational_choice`, and
`ClassicalUniqueChoice.dependent_unique_choice` dependencies. The choice
principles enter through existing complete-hitting witness selection;
guardedness itself does not assume the desired preservation result. No
new axiom or backend capability class is declared.

The full build, aggregate inventory check, and targeted joint kernel check
all passed locally. The stage-2 validation commands are:

```sh
python3 tools/check_aggregate.py
opam exec -- dune build
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Regression.Infrastructure.AllImports \
  -norec PTree.Eq.FreeOmega.GuardedInterp \
  -norec PTree.Regression.Semantics.GuardedInterp
```

The stage-2 inventory contained 194 modules (193 imports plus `AllImports`).
The kernel command loads their shared universe context but rechecks only
the three listed modules, not every existing proof in the repository.
The stored layout/client report reproduces exactly. No remote CI result
is asserted by this local validation record.

## Stage 3: atomic interpretation, a sufficient permutation profile

`Semantics/AtomicInterp.v` is a comparison-theory API; it is imported
directly, not exported as another canonical behavioral equivalence.
Neither peutt nor any transition/bisimulation definition changes.

The condition deliberately states a **sufficient profile, not a necessary
characterization of atomic handlers**. Source and target have the same
event interface. An `atomic_handler h` certificate supplies:

1. A response-type-preserving event permutation `rho` and its inverse.
2. Continuations `c_e : X -> ptree E MN X` for each `e : E X`.
3. Complete hitting `H(h(e)) = delta(Vis rho(e) c_e)`.
4. For every response `x`, complete hitting
   `H(c_e(x)) = delta(Ret x)`.

Here the equations mean the existing `ptree_stable_hitting` predicate with
the displayed `FORet` witness, not literal equality of representations.
The record is explicit data in `Type`, not a new backend typeclass. No
field assumes interpretation preservation or any bisimulation theorem.

Thus one source interaction becomes exactly one target interaction, with
the same response value. Before and after it there may be internal Tau/Prob
computation, with **no finite-fuel bound**. The complete behavior of each
segment is nevertheless the specified total Dirac measure. Unlike stage-2
guarding, this profile does not admit missing mass on these segments.
It does not require all syntactic branches to terminate: null branches can
be ignored by the underlying hitting semantics.

This first profile **does not cover event merging, changes of response
values, random selection of target events, or arbitrary effect signatures**.
In particular we do not claim that one visible interaction alone suffices
for every such generalization. The permutation lets each target action be
related to one source action through its inverse. For a many-to-one event
map, summing preimage action classes would need a different argument;
that obligation is not hidden in a new measure axiom.

### Direct transition proof

For a source stable head define the semantic head map:

```text
Ret r    |-> Ret r
Vis e k  |-> Vis rho(e) (fun x => c_e(x) >>= (interp h . k))
```

`atomic_interp_hitting` proves that interpretation maps the complete source
frontier by this function. `atomic_finish_bind` proves that the handler's
post-response internal segment disappears from complete hitting because
its behavior is `delta(Ret x)`.

`atomic_normalizes_trans` then transports any source transition witness to
any target transition witness by a graph coupling of these mapped heads.
It uses AE restriction and relational bind on the entire frontier. Missing
or disabled heads still contribute zero; all other masses keep their
original weights. There is no conditioning or normalization.

The coinductive candidate relates target trees whose complete behaviors
are mapped frontiers of some **transition-bisimilar** source trees. This
also covers selected mapped successor heads, not just literal `interp`
applications. Return and offered-event projections are transported
separately. For each target action, the inverse permutation provides the
source action; its source coupling is composed with the two graph
couplings. The successor candidate closes using `atomic_normalizes_head`.

The resulting endpoints are:

```coq
atomic_handler_guarded
atomic_candidate_postfixed
tree_trans_bisim_interp_atomic
```

The last theorem states, for an explicit certificate `atom` and any relation
`RR : R -> R -> Prop` on a **common** return carrier:

```text
tree_trans_bisim RR t u
  -> tree_trans_bisim RR (interp h t) (interp h u).
```

It invokes the existing transition GFP coinduction theorem directly, not
peutt soundness or fragment coincidence. The module imports existing
complete-hitting selection plumbing from `PEutt.v`; it never assumes
peutt of the source pair. Its backend is `MN / FreeOmega MN`, under the
same native Core, AE-lifting, Coupling-AE, Countable-AE and Omega
capabilities as stage 2.

### Checked boundaries and assumptions

`Regression/Semantics/AtomicInterp.v` checks:

- A handler with Tau before its interaction and a Dirac Prob/Tau response
  segment satisfies the semantic certificate, despite not being a bare
  syntactic `Vis e Ret`.
- This handler preserves the accepted 2x2 source pair, which is transition
  bisimilar but **not** peutt. Thus the test cannot be discharged by assuming
  the stronger source relation.
- A non-identity permutation exchanges two Boolean events and also two
  `Empty_set` events; its preservation theorem keeps arbitrary `RR`.
- `two_query_handler_not_atomic` rules out any certificate for the stage-1
  two-interaction handler: a certificate would contradict its independently
  proved transition-congruence counterexample.

`atomic_handler_guarded` inherits `eq_rect_eq`. The hitting/transition
mapping lemmas also inherit functional extensionality, relational choice,
and dependent unique choice. The postfixed/preservation endpoints and the
positive/negative regressions additionally inherit excluded middle from
existing totalized transition-witness existence. No axiom or backend class
is added. These are the results of `Print Assumptions`, not a claim of
constructivity.

Stage 3 stopped here for review; MDP preservation is developed separately
in stage 4 below. State interpretation remains unstarted.

### Stage 3 local validation

The full build and aggregate inventory guard passed (196 modules: 195
imports plus `AllImports`). The targeted joint kernel check also passed:

```sh
python3 tools/check_aggregate.py
opam exec -- dune build
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Regression.Infrastructure.AllImports \
  -norec PTree.Semantics.AtomicInterp \
  -norec PTree.Regression.Semantics.AtomicInterp
```

This loads the full-library universe context and rechecks the listed
modules, not every old proof. The layout audit has been regenerated and
reproduces exactly; no remote CI success is claimed.

## Stage 4: preserving the MDP fragment

`Semantics/MDPInterp.v` introduces a local semantic contract, not a fourth
interpreter semantics or a new equivalence. The generic section supports
`handler : forall X, E X -> ptree F MN X`, with distinct source and target
signatures. For a fixed return carrier:

```text
mdp_handler h :=
  forall selected source head a,
    mdp_head_E a -> mdp_state_F (ptree_interp_head_tree h a).
```

It asks that interpreting a qualifying **selected source stable head** give
one deterministic qualifying **target** state. It does not assume preservation for
arbitrary raw trees. `mdp_state_interp` derives that extension: the source
tree has a complete hitting measure semantically equal to a Dirac head;
the existing interp-hitting theorem and relational bind reduce its
interpreted frontier to the interpreted selected head. Hitting uniqueness
identifies the chosen witnesses. No atomicity or total-map premise is
needed for this head-to-tree extension.

The endpoint is `mdp_state_E t -> mdp_state_F (interp h t)`. Its original
hitting/bind proof is retained, with no new semantic assumption. The file
separates `GenericMDPInterp` (`E -> F`) from `AtomicMDPInterp` (`E -> E`).
This interface correction does not generalize `atomic_handler`, its inverse
label machinery, or the SubEnum atomic endpoints, and moves no directories.

The contract must still be discharged, and is not advertised as an
automatic fact about arbitrary handlers. We do so for the accepted atomic
permutation profile by a separate unary coinduction:

```text
candidate(a') := exists a, mdp_head a /\ a' = atomic_head a.
```

Return heads are terminal states, as before. For a Vis head and any
response, `atomic_finish_bind` and `atomic_interp_hitting` produce the
mapped source successor measure. AE closure follows from mapping the
source invariant; **totality must also be preserved**. Importantly, this
argument allows a distribution over many successor heads, not just a
Dirac successor, and uses no finite-interaction induction.

### Totality: an explicit backend boundary, discharged for SubEnum

The existing abstract `SemanticTotalProperLaws` only transports totality
along `sem_eq`. It does not assert that arbitrary value maps preserve
totality. Therefore `atomic_handler_mdp` and `mdp_state_interp_atomic`
expose the exact remaining measure-side obligation:

```text
forall mu, sem_total mu -> sem_total (atomic_map atom mu).
```

This is not a new axiom, a new backend class, or an assumption of the
desired MDP-preservation theorem. It is a capability premise of these
generic atomic endpoints. Other backends must discharge it before using
them; this stage makes no unconditional MathComp specialization claim.

`Prob/FreeOmegaTotalSubEnum.v` proves the stronger result for **every** map
`f : A -> B`, including non-injective maps:

```text
sem_total mu -> sem_total (free_omega_bind mu (fun x => FORet (f x))).
```

FreeOmega observable totality is witnessed by a semantically equivalent
representative and a total native observation. `subenum_observes_unit`
first forgets that observation's values, preserving its mass in a unit
observation. Its proof covers Ret, Zero, Sample, and increasing Lub;
the Lub case uses the existing rational indicator-test convergence.
The unit observation can then be carried through any value map, with no
inverse or injectivity assumption. Relational bind transports the
representative equivalence. The definition of `sem_total` is unchanged.

`Semantics/MDPInterpSubEnum.v` uses this fact to discharge the entire
measure-side premise. Its endpoints need only the explicit atomic
certificate, with no extra totality obligation for clients:

```coq
subenum_atomic_handler_mdp
subenum_mdp_state_interp_atomic
subenum_mdp_interp_peutt_tree_trans_iff
subenum_mdp_interp_transition_to_peutt
```

### Rejoining the compositionality results

`mdp_interp_peutt_tree_trans_iff` applies the **existing** fragment
coincidence theorem to the two preserved target states, with both relations
on signature `F`. It is an iff
between the two target relations, not a reflection theorem asserting that
interpretation preserves and reflects source behavior.

There are now two reusable routes:

- For a semantic `mdp_handler` that is also guarded, source coincidence
  gives `peutt_E`, stage 2 transports it through `E -> F`, and target
  coincidence recovers `tree_trans_bisim_F`
  (`mdp_guarded_interp_tree_trans`).
- For an atomic SubEnum handler, stage 3 preserves transition bisimulation
  directly, stage 4 preserves the fragment, and target coincidence recovers
  peutt (`subenum_mdp_interp_transition_to_peutt`).

Thus the earlier general strictness/congruence counterexamples remain
intact; it is the explicit source-and-target MDP restriction that lets the
two proof routes meet.

### Regression coverage

`Regression/Semantics/MDPInterp.v` uses a non-identity handler that flips
the `Reply` label, retains `Ask`, and includes the stage-3 internal Tau/Prob
response implementation. It checks a request followed by a genuinely
non-Dirac probabilistic successor, an infinite interacting service, delayed
initial states, terminal returns, and a non-injective totality map. The
transition-to-peutt example starts from the independently constructed
`delay_transition_bisim`, not peutt soundness. Neither `mdp_state` nor
`mdp_head` is changed.

The same regression module additionally declares separate `sourceE` and
`targetE` inductive families, with Boolean Ask and Boolean-indexed,
unit-response Reply events. The heterogeneous handler emits a Tau-prefixed
target event, negates the Reply label, and returns the unchanged response.
It has an independent unary-coinductive `hetero_handler_mdp` proof for all
source MDP heads; no atomic certificate or source=target identification is
used. The checks include general state preservation, guarded transition
preservation, target-fragment coincidence, and an actual infinite Ask/Reply
service with a delayed source counterpart. The latter is interpreted into
the distinct target family, not merely re-elaborated at the old signature.
`hetero_delay_transition_bisim` supplies the delayed source pair's evidence
by direct transition-GFP coinduction, matching return observations,
offered-event observations, and action successors using their Tau laws.
The infinite-service regression therefore starts from independent
`tree_trans_bisim_E` evidence; it no longer constructs that evidence via
`peutt_E` or `peutt_tree_trans_bisim`. The helper remains local to the
regression module, with no new public theorem or directory reorganization.

This stage does not start StateInterp or broaden the atomic profile.

### Stage 4 assumptions

The `Print Assumptions` audit distinguishes these endpoints:

- `mdp_state_interp`: existing `eq_rect_eq`, relational choice and dependent
  unique choice (no functional-extensionality or excluded-middle dependency).
- `subenum_observes_unit`: functional extensionality and the two choice
  principles, for selecting unit-observation witnesses.
- `subenum_free_omega_total_map`, `mdp_head_atomic`,
  `subenum_mdp_state_interp_atomic`, and the infinite-service membership
  regression: the same dependencies plus `eq_rect_eq`.
- The coincidence/compositionality routes additionally inherit excluded
  middle from the existing transition/fragment infrastructure.

No axiom, backend typeclass, unfinished proof, or change to totality is
introduced. The explicit generic `Htotal_map` premise is discharged by a
theorem at the SubEnum endpoints, not included in their assumption audit
as an unresolved constant.

The `E -> F` follow-up reruns this audit: the generic preservation,
target-coincidence and guarded-compositionality endpoints have exactly the
same dependencies as before generalization. The heterogeneous handler
contract and state-membership regressions use functional extensionality,
`eq_rect_eq` and the two existing choice principles; their transition and
coincidence endpoints additionally inherit excluded middle. No axiom,
source/target equality premise, or new backend capability is introduced.
The independent `hetero_delay_transition_bisim` helper inherits only
functional extensionality and `eq_rect_eq`; the final interpreted-service
endpoint retains the previously audited dependencies of the guarded route.

### Stage 4 local validation

The full build, 200-module aggregate inventory (199 imports plus
`AllImports`), and targeted joint kernel check all passed locally:

```sh
python3 tools/check_aggregate.py
opam exec -- dune build
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Regression.Infrastructure.AllImports \
  -norec PTree.Prob.FreeOmegaTotalSubEnum \
  -norec PTree.Semantics.MDPInterp \
  -norec PTree.Semantics.MDPInterpSubEnum \
  -norec PTree.Regression.Semantics.MDPInterp
```

This rechecks the four Stage 4 modules and the aggregate harness in the
full-library universe context, not every existing proof. The layout report
reproduces exactly. No remote CI success is asserted. Stage 4 now pauses
for acceptance before any StateInterp work.

The `E -> F` interface follow-up repeated all of these checks successfully,
including the original homogeneous regressions and new heterogeneous
contract, preservation, coincidence and infinite-service regressions.
The aggregate remains 200 modules. `AtomicInterp.v`,
`MDPInterpSubEnum.v`, and the total-map backend proof are unchanged; no
module or directory was moved. This follow-up is the candidate final
Stage 4 baseline, pending acceptance before layout-only work.

The regression-only independent-source fix repeated the full build,
aggregate inventory, the same targeted joint kernel check and assumption
audit successfully. The layout report is unchanged. Only the regression
and its documentation changed; the accepted generic and atomic theory
interfaces remain untouched. This fix awaits final Stage 4 acceptance.
