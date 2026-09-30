# Adaptive factory controller

The behavioral refinement is complete. This case is kept in one file,
`theories/Examples/AdaptiveFactoryController.v`; the previous
`FactoryController` example is unchanged.

Reading entry: `Adaptive.controller_program_rewrite`.

## Final contract

For every initial machine state `s` and rational target `0 <= q <= 1`:

```coq
PTree.bind
  (run_state (PTree.interp internal_handler (controller q)) s)
  (fun sa => Ret (snd sa))
≈ₚ controller_spec q0 q1.
```

The specification repeatedly performs:

```text
Request; native Bernoulli(q); Emit result; repeat
```

The final bind only projects the result interface after State interpretation.
It does not reset, resample or discard the running machine state. The stronger
`controller_refinement` compares the state-returning implementation directly to
the specification under `state_result sa a := snd sa = a`.

This is a behavioral theorem about infinite programs, not equality of finite
empirical frequencies. It is not a new extraction or host-PRNG correctness claim.

## Actual program

The implementation is an effectful PTree:

1. Select one of two biased sources using persistent machine health.
2. Draw the first bit; process a sensor report and possibly perform maintenance.
3. Draw the second bit from the **same selected source**.
4. Retry on equal bits, preserving updated health and counters.
5. Use the extracted bit in the existing binary rational-factory round.
6. Serve an infinite sequence of public `Request` / `Emit` interactions.

The false-bit probabilities are `1/3` and `1/4`. Internal handlers are finite,
deterministic and publicly silent. Interpretation first targets
`stateE machine_state +' publicE`, then `run_state` threads state. No reset
occurs between retries, factory rounds or public requests.

The sensor reports the first sampled bit deterministically. A failed
`true,true` attempt can change the next source. Successful final state depends
on the output bit. In particular, the proof does **not** factor the result into
an independent fair bit and a state distribution, nor merge the two failure
states into one retry state.

The contract concerns this concrete handler and these two sources. It does not
claim correctness for arbitrary diverging, mass-losing or publicly observable
internal handlers, or arbitrary adaptive positive biases. The public request
has a unit response and the target q is fixed throughout the service.

## Proof structure

```text
actual interleaved Prob / Vis / State attempt
    | lower_attempt, lower_attempt_kernel
exact stateful attempt kernel
    | lower_adaptive_normalized
actual stateful retry loop
    | complete-round summary + finite observations + support transport
adaptive_vn_fair : state/bit result related to a fair bit
    | rewrite State/handler equations; relational bind + iteration
    | existing rational factory correctness under interpretation
adaptive_factory_direct
    | inline the complete Request / factory / Emit / retry calculation
    | eventful relational iteration, arbitrary internal state
controller_program_rewrite
    | retain the state-returning interface as a consequence
controller_refinement
```

Program normalization uses the existing interpreter, State, bind, sampling and
iteration equations. There is no case-specific Proper instance, new capability,
or second proof of the rational factory's arithmetic. Generic heterogeneous
composition now belongs to `Eq/PEutt` as `peutt_rel_compose`; its derived
`peutt_rel_endpoint_Proper` lets ordinary equality equations rewrite both
endpoints of `peutt RR`. It needs only the existing frontier CoreLaws, not
native laws, bind/omega laws or a completion-specific instance.

The two reading points are:

- `adaptive_factory_direct`: rewrite the specification to the existing fair
  binary factory, expose State/interpreter iteration, then rewrite the actual
  factory body. Heterogeneous bind consumes `adaptive_vn_fair`; the invariant
  preserves the rational residual target while allowing any machine state.
- `controller_program_rewrite`: expose `lower_iter`, open one complete public
  request **inside the proof**, and rewrite handler, bind and visible-event
  equations. Relational bind consumes the factory certificate; relational
  iteration carries the actual resulting state to the next request. Finally
  the identity bind on the specification disappears by rewriting.

Neither `service_refinement` nor `controller_refinement` is a prerequisite of
the displayed calculation. The former remains a reusable single-request
corollary; the latter is recovered from the final theorem. The old
`lower_service`, `lower_service_iteration`, `service_iteration_related` and
step-wrapper ladder have been removed, not renamed into opaque helpers.

One `lower_internal` equation covers the five deterministic private events.
The one-use normalized-step proof is local to `lower_adaptive_normalized`;
elementary fair-frontier facts are proved at their analysis use sites. Genuine
finite convergence and support arguments remain named and separate.

Ordinary equality rewriting cannot discard correlated state. The relational
bind/iteration steps therefore remain explicit rather than being disguised as
rewrites. No proof that final state and bit are independent is used or claimed.

## Finite analysis and the actual hitting bridge

`attempts n s` is a complete finite experiment with **n attempts**, not n
primitive internal steps. It retains pending states and successful state/bit
pairs. Its mass is one, including pending outcomes.

The analysis proves:

- Both returned-bit masses agree at every finite horizon.
- Returned-false + returned-true + pending mass = 1.
- Pending mass is at most `(5/8)^n`, uniformly in the initial state.
- Each returned-bit mass equals half of one minus pending mass and tends to 1/2.

`loop_kernel` compiles the two native draws in one attempt. `loop_hits`
uses `iteration_frontier_summary_hitting`: the local certificate is proved
by two finite sampling laws and a return law, while the library supplies
iteration congruence and primitive-loop cofinality. No case-specific
primitive-fuel schedule remains. `loop_round_observation` identifies the
library's observation rounds with `output_row`; `output_row_factor` relates
these rows to the finite experiment, for arbitrary rational observables.

The complete `loop_heads` frontier remains in `FreeOmega`, retaining the
successful state/bit correlation. Only its bit projection has a finite
native limit. See [the summary interface](ITERATION_SUMMARY.md) for the
precise scope and recorded helper-level assumption changes.

Conceptually this is the return-only/native-kernel case of
[general frontier iteration](FRONTIER_ITERATION.md), with the
[classical iteration connection](RETURN_ITERATION.md). The existing convenience
theorem is not implemented by calling that new generic theorem: it still uses
behavioral iteration plus primitive-loop cofinality. We keep it because its
observation API fits the bit-only analysis. No full finite joint distribution
of successful state and bit is requested, and no independence is asserted.

For the short entry example and the relationship between program algebra,
frontier analysis and protocol coinduction, see [the case gallery](CASE_STUDIES.md).

`loop_hits` establishes the complete hitting witness. `loop_heads_observes`
proves its fair output observation, and `raw_loop_ast` proves its total mass.
Thus the limit calculation is connected to the program, not left as a separate
mathematical model.

The observer maps return heads to `Some bit` and visible heads to `None`.
The observation-level relation requires a shared `Some bit`, so it cannot
accidentally identify an offered event with a returned bit. The additional
`loop_heads_fair_support` proves both high-universe AE-support transports.
Only then does `loop_heads_fair_lift` construct the quotient lifting and
`adaptive_vn_fair` conclude heterogeneous peutt.

Strict positivity of each attempt's success alone would not suffice for
arbitrarily varying sources. Here the uniform bound is proved for both actual
sources; it is not an AST assumption.

## Backend and trust boundaries

The native backend is **SubEnumQ**, with observable **FreeOmega SubEnumQ** as
frontier. Every native distribution carries its mass bound; this includes
the state-dependent sources, finite iteration rows and the direct Bernoulli
specification. The two sources are additionally proved total.

`EnumQ` is used only at the finite-analysis boundary. `source_coin_raw` and
`BoundedFactory.fair_coin_raw` / `bernoulli_raw` show that adding the bound
certificate preserves the exact finite weighting (including order and zero
entries). There is no runtime backend conversion or normalization. The
bounded factory component reuses the old binary algorithm's scalar convergence
certificate through `rows_raw`, then proves its own `SubEnumQ` hitting and
behavioral endpoint. It does not import the old EnumQ factory equivalence.

Upper program proofs consume semantic relations and existing algebra. The
sampler-parametric factory control flow is backend-independent; only its
probability analysis selects a representation.

No new probability axioms, capability classes, admitted proofs or checker
relaxations are introduced. The original seven finite-analysis contracts are
closed under the global context. Behavioral endpoints inherit the existing
library's extensionality, dependent-equality and choice dependencies; compiled
signatures and per-endpoint assumptions are recorded in the factory contract
suite without extending the global logical-axiom whitelist.

The factory contract suite records the explicit Adaptive carrier migration
from EnumQ to SubEnumQ. Unrelated controller contracts stay unchanged; internal
helper shapes are not frozen. CI is not queried.

## Local verification of the program-calculation refactor

Baseline: `62338b6`. The program definitions, distributions, handlers and return
relations are unchanged. Nineteen internal declarations were consolidated into
their use sites or the single `lower_internal` equation; the genuine finite
convergence and frontier analysis remains explicit.

- Full `opam exec -- dune build -j 2`, including AllImports and extraction:
  passed. Existing extraction warnings remain. This is not a claim that the
  two pre-existing Gate M modules are universe-checked.
- All 148 Python tool tests: passed.
- Architecture, API surface, soundness source and contract metadata audits:
  passed. Module count and Gate M allowlist are unchanged.
- Factory suite: all 47 compiled type/assumption contracts unchanged,
  including all 21 Adaptive endpoints.
- Mainline suite: all 491 compiled type/assumption contracts unchanged.
  Generic algebra suite: 131 contracts passed; its 129 existing entries are
  unchanged and only the two generic endpoints below were appended.
- The new generic heterogeneous composition and endpoint Proper have only
  the existing `Eqdep.Eq_rect_eq.eq_rect_eq` logical dependency. No capability
  or logical-axiom whitelist was added; the minimal heterogeneous regression
  actually rewrites both endpoints without native/bind/order/omega laws.
- Joint `coqchk -norec` for `Eq.PEutt`, `Interp.Iteration`,
  `Examples.AdaptiveFactoryController` and `Regression.Semantics.GenericAlgebra`:
  passed. This checks these module bodies while trusting dependencies, not
  a recursive whole-library kernel audit.

CI was not queried.

## Historical verification: bounded-backend migration

- Full `opam exec -- dune build`, including AllImports: passed. Existing
  extraction opacity/output-directory warnings remain; the full build still
  includes the two pre-existing Gate M modules, not used by this case.
- 142 Python tool tests: passed, including a bounded-native-carrier boundary
  check and the unchanged extracted-controller tests.
- Architecture, public-surface and soundness source audits: passed.
- All 465 mainline compiled contracts: unchanged.
- Factory suite: 47 checked signatures/assumptions. The 19 Adaptive entries
  explicitly change carrier; their logical-axiom sets are unchanged. The
  other 22 old entries are unchanged. Six new entries protect the exact raw
  projections, source totality and bounded factory endpoint.
- Generic algebra suite: 131 checked endpoints. Only the sampler-factory
  Proper signature changes printing to include the newly explicit native
  parameter; its assumptions are unchanged.
- Joint `coqchk -norec` for `FiniteRecordExtensionality`, `BernoulliFactory`,
  `BoundedFactory`, and `AdaptiveFactoryController`: passed. This checks those
  module bodies while trusting compiled dependencies; it is not a recursive
  whole-library kernel audit.

The only shared changes are backend-parameterizing the two sampler-only
factory definitions and adding bounded-distribution versions of three exact
finite bind equations to the existing opt-in record-extensionality module.
Generic PTree semantics, probability interfaces, backend definitions, old
controller/extraction roots and Gate M are unchanged. No new audit script or
proof-mode classification is introduced. Other historical EnumQ program cases
have not been migrated by this change.
