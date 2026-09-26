# Interactive Bernoulli Factory Controller

One program connects exact probability, unbounded internal computation,
infinite interaction, response-dependent continuations, standard State,
device interpretation, quantitative observation and OCaml execution.
The implementation uses the existing VN-plus-binary-factory algorithm;
there is no second sampling algorithm or whole-controller coupling proof.

## Program and main result

`Examples/FactoryController/Controller.v` contains a small two-phase machine:

```
AwaitOrder --ReceiveOrder(j)--> Manufacturing(j)
Manufacturing(j): sample mode; RunMachine(j, mode)
  Pass   : increment completed; Ship(j); AwaitOrder
  Rework : increment retries; Manufacturing(j)
  Jam    : increment jams; Alarm(j); WaitReset; Manufacturing(j)
```

It uses ITree's `stateE counters`, not a new state vocabulary. The device
protocol is example-specific. The source returns `Empty_set` and runs forever;
each environment response determines a different continuation. In addition,
both VN and the outer binary factory can retry arbitrarily often. An
environment may request Rework or Jam forever. No environment fairness or
service termination assumption is used in the refinement theorem.

Start with **`Rewriting.v:factory_controller_program_rewrite`** for the full
program calculation, not the condensed corollaries in `Facts.v`. Its `Run`
notation expands to the actual complete execution context:

```coq
run_exception
  (run_state
    (PTree.interp device_handler
      (run_state (controller (embed sampler) pc) counts)) script)
```

Under this unchanged context the proof explicitly performs:

```
Factory(VN(p), q)
  -> Factory(Fair, q)                     VN analysis
  -> iter (bind (Prob fair Ret) round) q  unfold factory
  -> iter (Prob fair round) q             bind/Ret algebra
  -> iter (Prob (bind fair (ret ∘ round)) Ret) q
                                         native sampling algebra
  -> standard_binary_loop(q)              finite round-distribution identity
  -> Prob Bernoulli(q) Ret                binary-loop analysis
```

These are `setoid_rewrite` / equality rewrites in the complete closed program,
not applications of `controller_refinement` or
`scripted_controller_refinement`. The only two unbounded probability-analysis
endpoints used are `peutt_factory_vn_fair` and
`peutt_factory_standard_direct`. The finite identity
`fair_binary_round_measure` is just the exact two-outcome round calculation.
The `peutt_sample_bind` and `peutt_sample_map` equations belong to generic
`Eq/Algebra.v`: neither selects EnumQ nor FreeOmega. The unchanged program
contexts use generic `run_state_peutt_eq_Proper`, `peutt_interp_Proper`,
`run_exception_peutt_eq_Proper` and `peutt_iter_Proper`. Their FreeOmega
registrations are now provided once, for arbitrary native `MN`, by an opt-in
library module:

```coq
From PTree.Interp.FreeOmega Require Import Rewriting.
Import FreeOmegaRewriting.
```

The complete calculation declares **no instances, instance registrations or
hints**. Its `≈ₚ` is a local notation for raw `PEutt.peutt` with the observable
EnumQ/FreeOmega profile explicitly fixed; it does not use `canonical_peutt`.
The three application congruences (embedding, factory, controller) are exported
by their respective facts modules. No generic proof or probability certificate
is repeated here. See [generic algebra](GENERIC_ALGEBRA.md) for the distinct
probability premises and the opt-in registration boundary.

`scripted_controller_program_rewrite` specializes this full calculation to the
actual implementation/specification extracted to OCaml. The extraction proof
pin now points to this theorem. Both arbitrary initial state/script and the
rational source/target parameters are retained in the general theorem.

`Facts.v` retains the earlier convenient condensed proof:

```coq
Theorem controller_refinement : controller_impl ≈ₚ controller_spec.
Proof.
  unfold controller_impl, controller_spec.
  setoid_rewrite implementation_sampler_correct. reflexivity.
Qed.
```

The demo samples from the existing `third_to_two_fifths`, not directly from
2/5. The specification uses `direct_two_fifths`. `embed` only uses the ordinary
PTree interpreter to embed the existing empty event signature in the controller
signature; it does not replace the sampler's nodes.

The parametric theorem `rational_controller_refinement` covers arbitrary
rational target `0 <= q <= 1`, with source weights `pfalse,ptrue >= 0`,
`pfalse+ptrue=1` and `0 < pfalse*ptrue`. This is not arbitrary-real sampling.
The existing component theorems prove almost-sure internal completion under
these hypotheses; an individual extracted execution may still diverge.

## Theorem chain

| Layer | Checked endpoint / dependency |
| --- | --- |
| T1: biased draws to fair coin | Existing `peutt_factory_vn_fair` |
| T2: nested sampler to rational Bernoulli | Existing `peutt_factory_vn_direct`; concrete `implementation_sampler_correct` |
| T3: infinite controller refinement | `controller_refinement`, `rational_controller_refinement` |
| T4: effect interpretation | `state_controller_refinement`, `device_handler_refinement`, `scripted_controller_refinement` |
| Full program calculation | `factory_controller_program_rewrite`; extracted pair: `scripted_controller_program_rewrite` |
| T5: explicit next-device probability | `next_action_probability`, `factory_next_action_probability` |
| Node validity | `implementation_probability`, `specification_probability` |

The whole-controller proof consumes the existing generic `peutt_iter_direct_rel`
with the canonical FreeOmega relational-limit certificates. State and device
interpretation likewise consume maintained generic theory via its completion
specializations. No theorem-level axiom or backend capability is introduced.
Raw EnumQ is retained to reuse the exact old program; the probability invariant
is separately proved, not inferred from raw finite weights.

## Next observable action, not merely a returned Boolean

After receipt of job `j`, arbitrary internal VN/factory computation precedes
the next device action. `Observation.v` unfolds one controller phase and
algebraically replaces only the pre-Vis sampler. Its explicit normal frontier is

```
FOSample Bernoulli(q) (fun fast =>
  FORet (FHVis (RunMachine j fast)
    (fun reply => run_state (machine_cont sampler j reply) s)))
```

The entire response continuation is retained, with unchanged current counters
`s`; counters change only after the response. The `Pass/Rework/Jam` continuations
are not quotiented down to event labels.
`next_device_frontier` relates **any** complete hitting witness of the
implementation phase to this explicit frontier by `stable_head_rel eq peutt`.
Thus the head-level statement retains related whole continuations before the
numeric projection; it is not merely equality of event-label marginals.

The numeric theorem projects this frontier through the existing one-event
query API. For the concrete implementation, Fast has mass 2/5 and Safe has
mass 3/5. The parametric theorem gives `q` and `1-q`. Its `Prₜ` is a proved
finite-observation certificate, not an executable probability calculator.
The query witness of the implementation is related to the explicit normal
frontier by the existing equality lifting: no unsupported conversion from
`sem_lift eq` to literal `sem_eq` is claimed. The one-event selector's arbitrary
Pass reply does not run the continuation or condition on eventual shipping.

## Executing the same implementation

`Scripted.v` interprets the device into standard State plus an explicit
experiment-stop exception. It consumes an order queue and response script and
records accepted orders, modes, machine replies, shipments, alarms and resets.
Then the standard State and Exception interpreters produce a closed tree.
There is **no truncation of internal sampler retries**.

The demonstration script contains orders 17 and 23 and replies
`Rework, Jam, Pass, Pass`, thus exercising all branches. When the order queue
is exhausted, the harness returns its log through the explicit stop exception.
That is termination of a finite experiment, not termination of the source
controller, missing mass, entropy exhaustion, or a Timeout.

```
dune exec extraction/factory-controller/main.exe -- impl script 42
dune exec extraction/factory-controller/main.exe -- spec script 42
dune exec extraction/factory-controller/main.exe -- impl interactive 42
```

The live adapter accepts order numbers and pass/rework/jam responses and asks
for reset acknowledgement. Its typed extraction-side view exposes actual
device continuations; it does not add Vis handling to the closed Runner.
`--trace NEW_FILE` records requested ticket bounds and supplied indices. Replay
accepts a comma-separated index sequence. Different implementations need not
use the same entropy trace, seed, number of draws, or finite execution horizon.
The small host adapter rejects integer/ticket encodings above 100,000 as a
resource limit; this is not an internal-step budget or a semantic Timeout.

## Trust and scope

The extracted controller, samplers, effect eliminators and exact rational
ticket compiler are the actual formal definitions. The host scheduler, IO,
OCaml extraction/compiler/runtime and `Random.State` remain trusted. Runtime
statistics or deterministic script tests do not prove PRNG uniformity.
The existing ideal uniform-ticket/finite-runner theory is not silently claimed
as a new end-to-end theorem for this handwritten fuel-free scheduler.

The controller is not asserted to satisfy `mdp_state` at every phase, nor does
this case study claim unrestricted handler preservation for transition-only
bisimulation. Its canonical relation is whole-continuation `peutt`.
This is a vertical slice, not a proof that no other framework can express it.

The compiled assumption audit records the existing logical dependencies rather
than claiming a constructive proof. The refinement/quantitative chain inherits
functional extensionality, `Eqdep.Eq_rect_eq.eq_rect_eq`,
`RelationalChoice.relational_choice` and
`ClassicalUniqueChoice.dependent_unique_choice` from the existing probability
and algebra proofs. The latter two are explicitly listed for each affected
endpoint in the contract registry, not added to a global whitelist. There are
no new axioms, classes, probability capabilities or checker relaxations.

## Local validation

Baseline: `5a2b8fb`. All five application modules and the dedicated regression
are additions; existing mathematical/handler/backend implementations are
unchanged. The only pre-existing Rocq source edit adds the six sorted aggregate
imports. No new audit script, global hint or public API alias is introduced.

Full `dune build` (including AllImports and extraction) passed. All 134 Python
tool/execution tests passed, including eight new controller tests covering all
device reply branches, exact ticket replay, interactive continuations,
explicit experiment stop, and entropy/device errors distinct from Lost.
For the documented seed 42 script, the extracted factory used 34 native draws;
the direct specification used 4. These are runtime observations, not a
statistical correctness proof or a same-seed coupling claim.

The architecture now contains 432 modules, with the same two separately
allowlisted Gate M files; this case study is entirely Gate S. Source, public
surface and architecture checks passed. CI is outside this task's scope.

The 465 main compiled contracts and the 29 direct-iteration / 24
iteration-algebra safe-joint contracts are unchanged. Twenty new case-study
endpoints have exact compiled type and `Print Assumptions` snapshots. Joint
`coqchk -norec` passed for the five new application modules and their regression:
this checks six normally checked module bodies while trusting their compiled
dependencies, **not** an exhaustive recursive audit of the library.

### Full-program calculation follow-up

Relative to `f4873aa`, `Rewriting.v` adds the explicit calculation above without
changing the accepted controller, samplers, old Facts, observation theorem or
probability analysis. A regression consumes its concrete endpoint, and an
execution-tool test rejects replacing the calculation with an already composed
refinement theorem. The extraction proof pin uses the new endpoint; generated
`controller.ml` and `controller.mli` are byte-for-byte unchanged.

Local full build and all 135 tests passed. All 20 existing case-study compiled
contracts were compared unchanged; the two new contracts inherit exactly the
same logical-axiom set as the old closed-program refinement. The group now has
22 contracts. Architecture/source/public-surface checks passed (433 modules,
unchanged two-file Gate M allowlist). Joint `coqchk -norec` passed for Rewriting
and its regression, with dependencies trusted. No CI check was requested.
