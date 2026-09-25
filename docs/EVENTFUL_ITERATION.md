# Eventful behavioral iteration

Baseline: `b592fde`. This increment closes behavioral step congruence for
the actual `PTree.iter`, including visible and nonreturning steps. It does
not change iter, peutt, canonical routing, any probability interface, or
the handler machine and its previously checked adequacy proof.

## Result and use

Explicitly import the generic owner:

```coq
From PTree.Interp Require Import Iteration.
```

Its main theorem, under the probability profile below, is:

```text
peutt_iter_eventful_rel:
  (forall i j, SI i j ->
     peutt (pstruct_iter_sum_rel SI RR) (step1 i) (step2 j)) ->
  SI i j ->
  peutt RR (PTree.iter step1 i) (PTree.iter step2 j)
```

The state carriers `I1/I2`, return carriers `A/B`, state relation `SI`,
and return relation `RR` are genuinely heterogeneous. The sum relation
relates retries by `SI` and exits by `RR`; it does not relate retry to exit.
The target event signature and native probability carrier remain shared.
`peutt_iter_eventful` specializes to pointwise equality-return peutt.

No no-event, termination, almost-sure termination, visible guarding,
finite-state, supplied hitting witness, or generator-closure premise is
required of the steps. A step can interact forever without returning to
the loop, retry silently forever, lose probability mass, or return.
The theorem is about whole-continuation peutt, not tree_trans_bisim.

For canonical completion clients use:

```coq
From PTree.Interp.FreeOmega Require Import Iteration.

(* Given related steps and initial states: *)
eapply free_omega_peutt_iter_eventful_rel with (SI := state_relation).
```

The completion module only supplies the existing probability certificates;
there is no backend copy of the proof. Neither module is newly bulk-exported
through PTreeFacts. No notation, alias, global instance or hint is registered.

## Proof, and why the old candidate was insufficient

The old `Eq/Iter` rule is still a valid sufficient condition under a weaker
profile. Its candidate contains only pairs of loop-entry observations.
After a visible step response, the residual tree may instead be a return
or an arbitrary active continuation. Thus that particular candidate need
not contain the states needed by a direct behavioral-step argument.
The regression formally checks exclusion of a residual Ret; it does not
claim a newly proved countermodel to every possible closure rule.

The new proof uses an internal request protocol:

```text
request step i
  retry j -> request step j
  exit a  -> Ret a
```

Interpreting each request by the original step is structurally equivalent
to `Tau (iter step i)`. Interp guards before a step, whereas iter guards
after a retry; the leading Tau aligns the schedules. The structural proof
also includes an active-bind phase and works for infinite steps.
The protocol is proof infrastructure, not a new runtime implementation.

For two possibly different protocols the generic handler configurations
are related in three phases:

1. Entries carry `SI` on their current states.
2. Exits carry `RR` on their returned results.
3. Active steps carry the given `peutt (sum_rel SI RR)`, with the appropriate
   loop continuations attached.

Complete frontier coupling for active steps comes from `peutt_hitting_lift`.
A retry/exit becomes an internal machine transition to the corresponding
configuration. At a visible head each response re-enters the active-step
candidate. `stable_hitting_rel` couples complete machine runs; existing
`handler_machine_hitting_sound` transports both sides independently to
their interpreted trees. Finally structural protocol equivalence and Tau
transparency recover the unchanged native iter expressions.

This is not a recursive assumption that iter already preserves peutt. No
unguarded coinductive hypothesis is used when a step returns internally.
There is no induction on an infinite tree, new limit construction, or appeal
to external OmegaVal validation. A local heterogeneous endpoint-composition
helper instantiates existing `stable_hitting_bisim_compose`.

The owner is `Interp/Iteration.v` because it consumes handler-machine
adequacy. `Eq -> Interp` remains forbidden; no dependency exception is added.

## Actual requirements and logical assumptions

The compiled generic signature contains:

- Native `SemanticMeasure` / Core laws.
- Frontier Core / Bind laws and MixedMeasure operations.
- Frontier order, omega, cofinality, diagonal and Fubini laws.
- Bind-order and mixed-bind-order laws, directed cofinality, omega selection.
- Explicit `relational_mixed_bind`, `relational_zero`, `relational_lub`.

These are existing probability-level structures, not a new `IterLaws` or
congruence capability. The machine comparison itself does not require a
native SemanticMeasure: native Core and relational mixed-bind enter the
final structural protocol-to-iter bridge. No mathematical minimality claim
is made for this sufficient profile.

`iteration_protocol_iter` is closed under the global context. The generic
machine comparison and main iter endpoints inherit only
`Eqdep.Eq_rect_eq.eq_rect_eq`; they do **not** depend on
`Classical_Prop.classic` or the source ITree preservation proof. The FreeOmega
specializations additionally inherit existing functional extensionality;
finite-real clients inherit their native extensionality/choice foundations.
All are recorded in `EVENTFUL_ITERATION_CONTRACTS.json`; the existing
logical-axiom whitelist is unchanged.

SubEnumQ and SubEnumR discharge the completion profile. Direct MathComp
instantiates the *same* generic theorem in the already-whitelisted Gate M
regression file. It explicitly retains `MathCompCouplingGluing` and
`relational_lub`: this is **not** a proof of unrestricted MathComp relational
limit closure. Its unsafe-hierarchy flag and collapsed-universe session are
recorded separately, with the generic theorem as an untainted safe control.
No unchecked module is added; no safe module depends on Gate M.

## Tests and conservation

Regression covers distinct state/return carriers; repeated visible retry;
native sampling with a weak Tau change; zero mass; a probability-algebra
rewrite eliminating a Dirac draw after each visible response; endless silent
retry; a coinductive step that never returns; both finite backends; and
carriers strictly above Set. The generic-only import boundary rejects
FreeOmega, external validation and direct MathComp names.

The Dirac-draw test supplies its finite hitting witnesses explicitly. It
does not pull in the older generic `peutt_prob_ret` proof's extra choice
dependencies merely to construct this finite test premise.

The additive source audit freezes all 407 prior theory modules. It allows
only three new safe modules, three sorted AllImports entries, and one exact
append-only conditional client in the existing MathComp regression. Old
compiled snapshots are not regenerated. The previous ITree preservation
audit consumes this adapter, so older preservation gates remain intact.

## Remaining scope

This closes the eventful behavioral-step congruence question under the
stated profile. It does not resolve the direct MathComp relational-lub
obligation, prove the converse `peutt -> ITree.eutt`, add general iteration
axiom packaging, or change arbitrary-target Reader/Writer commuting laws.
Those are separate tasks, not hidden premises of this result. CI is outside
this increment's scope.

## Local verification

- Full `opam exec -- dune build`, including safe AllImports and unchanged
  extraction targets (the existing extraction warnings remain).
- All 327 Python tool tests, including ten new iteration mutation/boundary tests.
- Architecture and source-soundness audits: 410 modules, 408 Gate S and the
  same two Gate M modules; no unfinished proof or capability declaration drift.
- All 465 retained compiled contracts and 266 public owner/helper contracts
  unchanged; the previous 52 source-ITree contracts rechecked unchanged.
- The new 19 safe contracts and logical assumptions checked, plus the
  conditional direct MathComp endpoint and a generic safe control queried
  separately in the explicit Gate M session.
- Existing Gate M snapshot unchanged: 37 direct endpoints and 6 safe controls.
- Joint `coqchk -norec` for the three new safe module bodies. Dependencies
  are trusted; this is not a recursive whole-library audit or a Gate M
  universe-checking claim.
- `git diff --check`.

No remote CI was queried, modified, awaited, or counted as evidence.
