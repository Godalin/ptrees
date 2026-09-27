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
    | existing heterogeneous bind + relational iteration
adaptive_factory_fair
    | existing rational factory correctness under interpretation
adaptive_factory_direct
    | public-event equations
service_refinement
    | existing eventful relational iteration, arbitrary internal state
controller_refinement / controller_program_rewrite
```

Program normalization uses the existing interpreter, State, bind, sampling and
iteration equations. There is no case-specific Proper instance, new capability,
or second proof of the rational factory's arithmetic. The existing generic
heterogeneous composition helper is used explicitly for relational endpoint
transport.

The final calculation exposes `lower_iter`, applies the generic relational
iteration theorem with an invariant permitting every internal state, and
removes the final identity bind. Ordinary equality-based rewriting cannot
discard correlated state; the one relational loop argument is explicit rather
than disguised as a rewrite. Local Boolean case splits and probability analysis
are confined to the supporting lemmas in the same file.

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

## Local verification of the bounded-backend migration

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
