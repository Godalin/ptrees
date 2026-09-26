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
    | finite observations + cofinal hitting schedule + support transport
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

`loop_hitting_three` identifies one attempt with two sampling steps and the
retry Tau. `round_schedule` counts these three-step blocks and is cofinal.
`loop_hitting_observes` links those **actual PTree hitting approximants** to
the finite output rows. `output_row_factor` relates the rows to the already
proved finite experiment, for arbitrary rational observables.

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

The backend is EnumQ with observable FreeOmega. Concrete finite expectations
and support calculations belong to the analysis section; upper program proofs
consume semantic relations and existing algebra.

No new probability axioms, capability classes, admitted proofs or checker
relaxations are introduced. The original seven finite-analysis contracts are
closed under the global context. Behavioral endpoints inherit the existing
library's extensionality, dependent-equality and choice dependencies; compiled
signatures and per-endpoint assumptions are recorded in the factory contract
suite without extending the global logical-axiom whitelist.

The original 32 factory contracts remain frozen. Only the new stable
refinement/adequacy endpoints are added; internal helper shapes are not frozen.
CI is not queried.

## Local verification of the completed case

- Full `opam exec -- dune build`, including AllImports: passed. Existing
  extraction opacity/output-directory warnings remain; the full build still
  includes the two pre-existing Gate M modules, not used by this case.
- 141 Python tool tests: passed.
- Architecture, public-surface and soundness source audits: passed.
- All 465 mainline compiled contracts: unchanged.
- Factory suite: 41 checked signatures/assumptions, including the 32 previous
  entries preserved exactly and nine new semantic/refinement endpoints.
- `coqchk -norec PTree.Examples.AdaptiveFactoryController`: passed. This checks
  the case module's proof bodies and trusts compiled dependencies; it is not
  a whole-library recursive kernel audit.

Only this example's formal source is extended. Generic theory, probability
interfaces, backend definitions, the old controller and extraction roots are
unchanged. No new audit script or proof-mode classification is introduced.
