# Adaptive factory controller

Status: checked implementation and adaptive-retry foundations; **not yet a
completed controller refinement**. The earlier `FactoryController` case remains
unchanged. This case is kept in `theories/Examples/AdaptiveFactoryController.v`.

## Program and interface

The source is an actual effectful PTree, not just a finite probability model:

1. Select one of two biased sources from persistent machine health.
2. Draw the first bit; process a sensor report and possibly perform maintenance.
3. Draw the second bit from the **same selected source**.
4. Retry on equal bits, preserving updated health and counters.
5. Use the resulting bit in the existing binary rational-factory round.
6. Serve an infinite sequence of public `Request` / `Emit` interactions.

The false-bit probabilities are `1/3` and `1/4`. Internal handlers are finite,
deterministic and publicly silent. Interpretation first targets
`stateE machine_state +' publicE`, then `run_state` threads the state. No reset
occurs between retries, factory rounds or public requests.

The sensor currently reports the first sampled bit deterministically. It is a
concrete internal protocol, not a claim about arbitrary sensor handlers. A failed
`true,true` attempt can change the next source. Successful final state depends
on the output bit: we do **not** replace the joint result by an independent fair
bit and state distribution.

## Checked program equations

- `lower_attempt`: interpretation of the real effectful attempt is two native
  draws with the exact state/result update.
- `lower_attempt_kernel`: algebraic flattening into its finite joint kernel.
- `lower_adaptive_normalized`: interpretation of the actual infinite retry loop
  is iteration of the explicit stateful step. This uses the existing generic
  interpreter and State iteration equations, without a new local Proper instance.

These proofs use program rewrites; the finite effect analysis additionally
splits Boolean branches. Native expectation calculations are confined to the
analysis part of the same file.

## Checked finite analysis

`attempts n s` is a mathematical experiment with **n complete attempts**, not
the PTree internal-fuel approximant. Its outcomes retain either the pending state
or the returned state and bit.

- `attempts_total`: total mass is one, including pending outcomes.
- `attempts_symmetric`: the two returned-bit masses agree for every n and state.
- `attempts_partition`: the two returned masses plus pending mass equal one.
- `adaptive_pending_bound`: pending mass is at most `(5/8)^n`.
- `adaptive_pending_vanishes`: that pending mass tends to zero.
- `attempts_return_probability`: each returned-bit mass is half of one minus
  pending mass.
- `adaptive_return_limit`: each returned-bit mass tends to `1/2`.

The uniform retry bound is proved for both concrete sources. Positivity of each
attempt's success alone would not suffice for an arbitrarily adapting source.

## Remaining proof obligations

The definitions `eventful_factory`, `controller` and `controller_spec` exist,
but their final equivalence is **not proved** in this increment.

The next substantive step is to relate complete-attempt experiments to the
normalized loop's actual stable-hitting approximants (allowing a cofinal fuel
change), and derive the fair **output marginal** while retaining state
correlation. The finite-analysis limit alone is not asserted to be that hitting
semantics. Then lift the state-indexed result through the outer rational factory
and the infinite public service. State erasure must be justified relationally;
equality of output marginals does not license discarding arbitrary state effects.

There are no new probability axioms, capability classes, admitted proofs or
checker relaxations. Compiled endpoint signatures and logical assumptions are
recorded alongside the existing factory contracts. No CI claim is made.

The seven finite-analysis contracts are closed under the global context. The
three program equations inherit the existing library's functional extensionality,
`eq_rect_eq`, relational choice and dependent unique choice. Those choices are
recorded per endpoint, without extending the global logical-axiom whitelist.

## Local validation of this increment

- Full `opam exec -- dune build`, including safe AllImports: passed. Existing
  extraction opacity/output-directory warnings remain.
- 141 Python tool tests: passed.
- Architecture, public-surface and soundness source checks: passed.
- 465 existing mainline compiled contracts: unchanged.
- Factory suite: 22 existing contracts unchanged, 10 new contracts checked.
- `coqchk -norec PTree.Examples.AdaptiveFactoryController`: passed. This checks
  the new module body while trusting its compiled dependencies; it is not a
  whole-library recursive kernel audit.
- No CI query or remote validation claim.
