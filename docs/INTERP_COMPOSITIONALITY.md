# Interpretation: staged compositionality work

Each stage stops for review before the next one starts. No new equivalence,
transition semantics, heterogeneous-effect framework, or general StateT
library is part of this work.

| Stage | Deliverable | Status |
| --- | --- | --- |
| 1. InterpExposure | Decide whether arbitrary interpretation preserves `tree_trans_bisim` | Counterexample proved; awaiting review |
| 2. GuardedInterp | Semantic visible guarding, then `interp_vis_fusion` and peutt preservation | Not started |
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

The public regression endpoints are:

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
  conditional on `interp_vis_fusion`; stage 2 has not been implemented here.
- This is a bisimulation (rather than linear-trace) obstruction. It does not mean one run
  queries the source continuation twice, nor does this proof claim a
  distinguishing linear finite-interaction probability.

## Validation

The full build passed, including the new module in `AllImports`, whose inventory
guard now covers all 191 other modules. The new endpoints inherit exactly
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
