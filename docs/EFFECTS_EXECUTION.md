# Standard effects and executable PTree interpretation

## Current status

Implementation chain through `145a9c9`, now extended by the
[finite runner probability bridge](RUNNER_DISTRIBUTION.md) from baseline
`892a6d3`. This is the current status entry point
for effects, handlers and execution; linked stage reports retain their own
historical baselines and validation results. The original operational
checkpoint began at `7b4c9714bb3845ed283a68fd084a6b4b33073e6f`.

The [fuel-free simulation follow-up](UNBOUNDED_SIMULATION.md) now extracts
the existing proved-equivalent Von Neumann and direct-fair programs into a
separate OCaml executable. It supplies live random execution, statistics,
and streamed replay without a transition budget. This is an executable
demonstration with explicit host trust boundaries, not an extension of the
finite runner correctness theorem. All old extraction targets are retained.
The same executable now includes the nested Bernoulli factory and its
direct 2/5 specification, linked to the existing assumption-explicit
compositional equivalence theorem; no factory algorithm is rewritten in OCaml.

The implementation goal is complete: proved rewriting can be followed by
effect elimination, extraction and replay. **The finite runner distribution
is now proved under an explicit history-conditional uniform entropy model;
its returned projection and limit agree with hitting semantics.** This does
not verify the OCaml PRNG. Completing these goals does not complete every item in
the original theory/execution proposal. CI remains out of scope unless
explicitly requested; no environment changes are planned.

| Item | Current status | Scope |
| --- | --- | --- |
| Arbitrary fixed-handler peutt preservation | Proved | Heterogeneous results and effects; requires the relational-limit profile. |
| Pointwise behavioral handler replacement | Proved | Two handlers, heterogeneous results; the same generic relational-limit profile. |
| Handler composition and sum calculus | Proved | Pure combinators; units/associativity, case and bimap congruence modulo pointwise peutt. |
| ITree sampling-effect elaboration | Proved basic laws | Actual ITree source to native Prob; Ret/Tau/Vis/bind/iter and target-handler postcomposition. Source eutt preservation remains separate. |
| Interpreted effect algebra and probability interaction | Proved finite equations | Four State laws, Reader contraction, ordered Writer unit/fusion, Exception left-zero; no unconditional sample-before-throw erasure. Transformer agreements beyond State remain pending. |
| State peutt preservation | Proved | Same initial state; equal final states and related results. |
| Reader / Writer / Exception | Implemented and proved | Basic clients and preservation, not a complete effect algebra. |
| Separate Vis/Prob fold and StateT commutation | Proved | Lawful target with iteration uniformity; checked ITree instance. |
| Finite runner | Proved operationally | Returned/Lost paths relative to the supplied sampler. |
| General rational tickets | Proved for one draw | Exact native distribution under a uniform bounded index. |
| State+Prob rewrite, extraction, seed/replay | Implemented and checked | No same-seed, same-trace or same-fuel equality claim. |
| Finite runner probability correspondence | Proved under conditional uniform entropy | All finite outcomes; returned projection agrees with same-fuel hitting, and its limit with complete hitting. Not PRNG verification. |
| Fuel-free proved-sampler simulation | Implemented and tested | Extracts the actual Von Neumann/direct-fair theorem roots. Handwritten scheduling and PRNG remain trusted; individual runs may diverge. |

The [handler-calculus follow-up](HANDLER_CALCULUS.md) now makes pointwise
behavioral handler equivalence a first-class relation. Its generic two-machine
proof subsumes fixed-handler preservation, and its FreeOmega clients reuse
existing model obligations. The program/reasoning entry points expose actual
owners, including State/Reader/Writer/Exception; no alias shadowing is introduced.
Generic arbitrary-target fold algebra remains deferred: MonadIter alone does
not entail monadic interpretation or probability-respecting laws.

The [ITree bridge](ITREE_BRIDGE.md) now internalizes `Sample mu` as native
`Prob mu`, with an actual two-coins ITree example and an unbounded retry
iteration law. This is distinct from the existing PTree-to-ITree execution
fold. It does not claim a general source-ITree `eutt` preservation theorem.

The [effect-algebra increment](EFFECT_ALGEBRA.md) adds generic interpreted
equations and a half-mass exception counterexample, without changing the
existing eliminators. Writer is still implemented through State, not WriterT.
Its new bind law threads an accumulator; canonical transformer iteration and
Reader/Writer/Exception fold agreement remain separate obligations. An actual
ITree Sample/Get/Put example now follows both existing State interpretation
routes. Probability interaction clients retain the already-audited classical
choice dependencies of generic `peutt_prob`; they are not claimed axiom-free.

The earlier [arbitrary-handler increment](UNRESTRICTED_INTERP.md) closes
the fixed-handler eliminating/mixed fusion obligation, using a two-phase
machine and checked finite/limit scheduling. It proves heterogeneous peutt
preservation for arbitrary handlers under the existing relational-lub profile.
The [State-indexed follow-up](STATE_PRESERVATION.md) separately proves
arbitrary heterogeneous `run_state` peutt preservation, including local
setoid rewriting. [StateT/fold commutation](STATE_FOLD.md) is now proved
from ordinary monad laws and pure-map iteration uniformity, with ITree as
a checked target model. [Rational tickets](RATIONAL_TICKETS.md) now prove
general single-draw distribution correctness and provide a second extracted
State example with random/seed/replay modes. The subsequent
[finite probability bridge](RUNNER_DISTRIBUTION.md) composes these laws with
the actual replay runner and existing hitting adequacy.

The [end-to-end State rewrite](STATE_REWRITE.md) now fuses two probability
nodes before State elimination, proves preservation through the handler,
and extracts both theorem-linked programs. It explicitly tests the differing
fuel/entropy requirements rather than asserting same-seed execution equality.

[Standard effects](STANDARD_EFFECTS.md) now add Reader, Writer and Exception
clients using ITree's event definitions. Reader/Writer preservation composes
the existing handler/State results; early exceptions are explicit returned
errors, proved by stable-head projection rather than a void-returning handler.

## Implemented chain

```
ITree stateE/Get/Put + native Prob
                  |
             run_state
                  |
        closed PTree void1 SubEnumQ
                  |
     rational interval replay / uniform-index tickets
                  |
         finite verified runner
                  |
          extracted OCaml program
```

`Interp/State.v` reuses ITree's event and subevent definitions. It does not
declare another state effect. `run_state` threads the state, preserves
native `Prob`, forwards the remaining events, and replaces handled Get/Put
with one `Tau`. Return values are state-first pairs, matching ITree's
`Monads.stateT` convention.

`StateFacts.v` proves the six constructor equations, heterogeneous
`pstruct` preservation, and the State/bind equation. `StateStrong.v` proves
heterogeneous `pstrong` preservation using native relational lifting.
The return relation is equal final states together with the supplied result
relation. These are actual structural preservation theorems, **not**
arbitrary source `peutt` preservation.

The subsequent `StateIter.v` follow-up proves `run_state_iter`: eliminating
State around `iter step i` is structurally equivalent to iterating over
the combined `(state, loop-index)` carrier. The transformed step runs the
original body at the current state, then routes **its returned updated
state** to either the next index or the final result. The theorem accepts
arbitrary native probability and unhandled visible events, with no measure
capabilities or logical axioms. Replay regressions check both sides on a
two-attempt stateful probabilistic loop, alongside an eventful client.

`Core/Fold.v` defines a Monad/MonadIter consumer with two distinct algebras:

* `handle : E ~> T` for visible effects;
* `sample : MN ~> T` for native probability.

Probability is never encoded as a visible event. `Interp/StateFold.v`
instantiates these algebras in the existing ITree `Monads.stateT`, with
Get/Put, forwarding, and state-preserving native sampling. The local
equations are definitional; Monad/MonadIter operations alone do not prove
fold laws or full State/fold commutation. `StateFoldFacts.v` now supplies
that theorem under explicit iteration uniformity; `Execution/ITreeFold.v`
proves the required law for ITree and the separate Vis/Prob fold equations.

## Finite execution contract

`Execution/Runner.v` is parameterized by a deterministic native sampler
and an entropy state. It only consumes closed trees. It distinguishes:

| Outcome | Meaning |
| --- | --- |
| `Returned a` | Program returned; remaining entropy is retained. |
| `Lost` | The native sampler selected missing mass; no retry or normalization. |
| `Timeout` | Transition fuel exhausted; no sampling occurs at zero fuel. |
| `EntropyExhausted` | Provider cannot supply another draw; the ticket adapter also uses this for an invalid index. |

Ret costs no fuel. Tau and Prob each cost one transition. Handled State
events therefore cost fuel but do not consume entropy.

The inductive `executes` relation has no fuel and describes finite
Returned/Lost paths relative to that same sampler. Theorems establish:

* terminating runner result implies an operational path;
* each finite operational path is found with sufficient fuel;
* an iff combining these directions;
* more fuel preserves a finished result **and its remaining entropy**.

This is operational correctness relative to the sampler. It is not a
statement that an arbitrary oracle implements the native probability law,
nor an equality with the complete stable-hitting measure. In particular,
timeout is not a proof of divergence or lost probability mass.

## Rational replay and the executable example

`Execution/Backend/SubEnumQ.v` scans the actual finite rational entries
against a checked quantile in `[0,1)`. Lower interval endpoints are included,
upper endpoints excluded. There is no floating-point arithmetic, resampling,
deduplication, or rescaling to total mass one.

`replay_sample_support` proves that a selected value occurs with a positive
coefficient. `replay_sample_missing` proves exactly:

```
sample mu q = Missing  <->  mass(mu) <= q.
```

This interval adapter supplies a correct selector and deterministic replay,
**not by itself a uniform random sampler for arbitrary rational weights**.
An arbitrary sequence of rational quantiles is not a continuous uniform
random variable. The separate ticket adapter now proves the exact general
single-draw law under a uniform bounded-index assumption; see
[Rational tickets](RATIONAL_TICKETS.md).

`Examples/StateCounter.v` contains a fair-coin tick and a recursively
defined counter that increments state and retries until the coin succeeds.
It proves the explicit state-eliminated tick equation and checks actual
two-attempt execution, timeout, replay exhaustion and unused entropy.
`replay_two_attempts_path` connects the computation to `executes`.

The original `state-counter` executable exposes only this fixed fair-coin program. A false bit maps
to quantile 1/4, a true bit to 3/4. `coin_selects_bit` and
`coin_bit_expectation` prove the local correspondence with its native fair
distribution. This two-quantile construction is deliberately **not exposed
as a uniform sampler for arbitrary SubEnumQ distributions**.

```
opam exec -- dune build extraction/state-counter/main.exe
opam exec -- dune exec extraction/state-counter/main.exe -- replay 7 0 010
# Returned 2
# remaining=1
# replay=010

opam exec -- dune exec extraction/state-counter/main.exe -- seed 40 0 42 10
# Prints the supplied bit trace, which can be passed to replay.
```

`counter.ml` and its interface are generated only in `_build`. The PTree,
state interpreter, rational selector, and runner are extracted, not
reimplemented in OCaml. The handwritten driver parses input and provides
bits. `Random.State` is a pseudorandom implementation, not a verified
mathematical uniform oracle. The printed replay is the reproducible
interface. No claim of cryptographic randomness is made.

Extraction uses Coq's standard basic-type mappings and keeps inductive
naturals, rather than silently replacing verified arithmetic with bounded
machine arithmetic. Extraction's warning about accessing opaque bodies is
separate from universe checking: no checker relaxation is added. The
extracted impossible `Vis` case on `void1` is not an external probability
axiom. There are no unrealized-axiom stubs in the generated executable.

## Follow-up queue (not implemented by this documentation cleanup)

1. **Finite-runner probability correspondence — completed in the ideal
   conditional model.** [The bridge](RUNNER_DISTRIBUTION.md) proves the finite
   outcome law, same-fuel returned hitting projection and complete-hitting
   limit. Explicit Lost, Timeout and divergence remain distinct. No claim is
   made that the external PRNG meets the conditional uniformity premise.
2. **Efficient sampling refinement and error classification — next execution
   priority.** Replace denominator-product ticket materialization by an
   integer-weight interval implementation, proving equivalence to the current
   reference law. Distinguish invalid entropy from exhausted entropy. The
   present extracted implementation can expand enormous lists, including
   while computing a ticket count; the host bound is not a proved resource
   bound on this work.
3. **Fold/runner connection and application-driven effect laws — deferred.**
   Relate finite execution to fold where appropriate. Arbitrary-fold peutt
   preservation needs probability-respecting sampling laws, not just monad
   laws. General state relations, effect-order laws and richer Writer/Exception
   algebra are not yet supplied.
4. **Separate theory backlog — deferred.** Generic eventless behavioral iter,
   Atomic/MDP consumer cleanup and final assumption minimization are not
   reported as completed by the execution work. Do not reopen foundational
   interfaces merely to obtain backend symmetry.

The probability bridge does not start the remaining execution optimizations.
Update this section when their status changes and link the corresponding
proof/report instead of leaving contradictory pending lists in stage reports.

## Assumption and trust boundaries

Arbitrary-handler and State preservation consume order/omega, cofinality,
bind-order, diagonal/Fubini, selection and relational-limit capabilities.
These are proved model obligations where instances exist, not a claim that
the hypotheses are minimal. FreeOmega supplies relational-lub closure;
unrestricted MathComp closure remains a separate obligation, and MathComp
coupling gluing is still explicit. The two Gate M files retain their accepted
local universe-checking relaxation; safe mathematics does not depend on them.

StateT-fold commutation requires iteration uniformity, proved for ITree.
The State rewrite inherits the existing fusion theorem's relational and
dependent unique choice, as well as the concrete specialization's
extensionality/eq_rect_eq dependencies; see [its audit](STATE_REWRITE.md).
The rational ticket law does not verify OCaml PRNG fairness. Extraction,
the OCaml toolchain/runtime and the handwritten entropy provider remain
explicit execution trust boundaries.

## Isolation and historical validation

The counts and commands below describe the initial operational checkpoints,
not a new validation run or current whole-repository counts. Later validation
is recorded in the linked stage reports; the latest implementation report is
[Runner distribution](RUNNER_DISTRIBUTION.md).

Generic `Execution` depends only on itself and Core. Its concrete rational
adapter can consume finite representation mathematics, but not FreeOmega,
external OmegaVal validation, or the PTree equality theory. Core/Eq/Interp
cannot depend back on execution. Existing Gate M remains exactly two files.

`audit_effect_execution.py` freezes all 328 baseline theory files byte for
byte except the twelve exact sorted aggregate additions. Its State/iter
follow-up also freezes the first ten new operational files at `b23c852`.
The previous migration
gates consume a checked additive projection, not relaxed source comparisons.
The new snapshot checks 44 compiled endpoints (the first forty unchanged
from `b23c852`). Of those, only the two
structural relation-preservation proofs inherit existing `eq_rect_eq`;
the other 42 are closed under the global context.

Validation commands (build once before tool/executable tests):

```
opam exec -- dune build
python3 tools/audit_effect_execution.py --compiled
python3 tools/audit_architecture.py --check
python3 tools/audit_soundness.py --source-only
python3 tools/audit_assumptions.py
python3 -m unittest discover -s tools -p 'test_*.py'
```

Targeted joint `coqchk -norec` checks the new safe module bodies with their
dependencies trusted. It is not a full recursive whole-library kernel audit
and never includes Gate M.

Local `b23c852` checkpoint results: full build (including AllImports and the extracted
executable), 191 tool/executable tests, architecture/source checks, all 465
unchanged main contracts, the 40 new compiled contracts, and the ten-module
joint `coqchk -norec` passed. There are 338 theory modules: 336 Gate S and the
unchanged two Gate M modules. The targeted checker used VM conversion for
native-compute proof bodies; this is not an unchecked proof bypass.

State/iter follow-up: full build and AllImports, 44 compiled contracts,
14 focused audit/executable tests, architecture/source conservation, and
the two-new-module joint `coqchk -norec` passed. There are now 340 modules
(338 Gate S, the same two Gate M). The full 191-test and 465-main-contract
checks were run at `b23c852`; the follow-up keeps those operational sources
and main snapshots frozen and does not report a second full-suite run.
