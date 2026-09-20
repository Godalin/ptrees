# Interpretation: staged compositionality work

Each stage stops for review before the next one starts. No new equivalence,
transition semantics, heterogeneous-effect framework, or general StateT
library is part of this work.

| Stage | Deliverable | Status |
| --- | --- | --- |
| 1. InterpExposure | Decide whether arbitrary interpretation preserves `tree_trans_bisim` | Accepted baseline `4703035` |
| 2. GuardedInterp | Semantic visible guarding, then `interp_vis_fusion` and peutt preservation | Proved; awaiting review |
| 3. AtomicInterp | A sufficient atomic-handler contract for transition preservation | Not started |
| 4. MDPInterp | An explicit handler contract preserving `mdp_state` | Not started |
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

Stage 3's atomic-handler definition and theorem remain unstarted. In
particular, this result does not strengthen the known false transition
congruence claim or establish arbitrary-handler peutt preservation.

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

The inventory now contains 194 modules (193 imports plus `AllImports`).
The kernel command loads their shared universe context but rechecks only
the three listed modules, not every existing proof in the repository.
The stored layout/client report reproduces exactly. No remote CI result
is asserted by this local validation record.
