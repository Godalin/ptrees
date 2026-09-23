# Standard effects and executable PTree interpretation

Baseline: `7b4c9714bb3845ed283a68fd084a6b4b33073e6f`.
This is an additive operational checkpoint, not completion of the whole
handler-preservation roadmap. Existing probability/equality/interpreter
theorems and both mainline/MathComp contract snapshots are unchanged.
No CI or environment changes are included.

The subsequent [arbitrary-handler increment](UNRESTRICTED_INTERP.md) closes
the fixed-handler eliminating/mixed fusion obligation, using a two-phase
machine and checked finite/limit scheduling. It proves heterogeneous peutt
preservation for arbitrary handlers under the existing relational-lub profile.
The [State-indexed follow-up](STATE_PRESERVATION.md) separately proves
arbitrary heterogeneous `run_state` peutt preservation, including local
setoid rewriting. Full StateT/fold commutation and general sampler
distribution correctness remain open.

## Implemented chain

```
ITree stateE/Get/Put + native Prob
                  |
             run_state
                  |
        closed PTree void1 SubEnumQ
                  |
     exact rational interval replay
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
fold laws or full State/fold commutation.

## Finite execution contract

`Execution/Runner.v` is parameterized by a deterministic native sampler
and an entropy state. It only consumes closed trees. It distinguishes:

| Outcome | Meaning |
| --- | --- |
| `Returned a` | Program returned; remaining entropy is retained. |
| `Lost` | The native sampler selected missing mass; no retry or normalization. |
| `Timeout` | Transition fuel exhausted; no sampling occurs at zero fuel. |
| `EntropyExhausted` | Replay/provider cannot supply another draw. |

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

This supplies a correct interval selector and deterministic replay, **not
yet a verified uniform random sampler for arbitrary rational weights**.
An arbitrary sequence of rational quantiles is not a continuous uniform
random variable.

`Examples/StateCounter.v` contains a fair-coin tick and a recursively
defined counter that increments state and retries until the coin succeeds.
It proves the explicit state-eliminated tick equation and checks actual
two-attempt execution, timeout, replay exhaustion and unused entropy.
`replay_two_attempts_path` connects the computation to `executes`.

The executable exposes only this fixed fair-coin program. A false bit maps
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

## Deliberately open work

1. **Eliminating/mixed handler fusion.** Existing guarded fusion can discard
   return heads on AE support. An eliminating handler cannot: its return
   enters the interpreted source continuation before a new target visible
   guard. Assuming those continuations already `peutt`-related would be
   circular. A complete finite-collapse/cofinality argument is still needed.
   No theorem-level capability has been added to hide this obligation.
2. **State behavioral preservation and fold.** The structural bind, iter and
   pstrong results above do not prove `peutt t u -> peutt (run_state t s)
   (run_state u s)`. Full StateT-fold commutation remains open.
   State is a stateful transformer, not a fixed value-returning handler.
3. **Reader/Writer/Exception.** Reuse the existing ITree signatures. Exception
   early exit must change the result type; it cannot manufacture a response
   to an empty-response Throw event. These clients are not implemented here.
4. **General rational randomness and hitting correspondence.** Construct
   denominator-indexed uniform tickets, prove their full native distribution
   law, and then connect operational finite paths to probability/hitting.
   Local fair-bit correctness is not a substitute for this general theorem.

The goal remains active. This checkpoint makes the operational end-to-end
path testable without claiming that the unresolved semantic bridge is done.

## Isolation and validation

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
