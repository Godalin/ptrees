# Exact rational tickets and extracted stateful execution

Baseline: `09a1773`. The existing quantile/replay sampler remains unchanged.
This increment adds a general, executable finite rational sampler, rather
than treating two fair-coin quantiles as a sampler for every native node.

## Construction and exact probability law

For each nonnegative rational entry `p`, the compiler reads `numq p` and
`denq p`. The product of denominators gives a positive integer `d`, and an
entry is expanded into exactly `p*d` value tickets. This is constructive
Rocq computation, with no existence oracle, classical choice, floating point,
sorting, deduplication, or normalization. Zero entries contribute no tickets;
repeated values keep their separate contributions and original order.

`compile_tickets_expectation` proves, for every signed rational test `f`:

```
sum f value_tickets = d * finite_expect f original_entries
```

The subprobability bound implies the value-ticket count is at most `d`.
The compiler fills the remaining positions with `None`, producing **exactly
`d` tickets**. The empty distribution has `d=1` and one missing ticket, so
even an empty value carrier is supported without inventing a value.

`draw_ticket mu i` selects the corresponding position. For a uniform index
`0 <= i < d`, `uniform_ticket_expectation` establishes the full law:

```
E[f(draw_ticket mu i)]
  = finite_expect (fun x => f(Some x)) mu
    + (1 - mass mu) * f(None)
```

This holds for arbitrary carriers and arbitrary signed rational tests.
`uniform_ticket_returns` and `uniform_ticket_loss` specialize it to returned
values and exactly the missing mass. There is no conditioning on success.
The entire rational compiler/distribution proof is closed under the global
context: no additional logical or probability axioms occur.

## Entropy interface and executable scope

`ticket_sample` asks its provider for an integer with the current required
bound. A valid index selects `Drawn` or `Missing`; a missing or out-of-range
token produces `NoEntropy`. In the runner those become `Returned`/continued
execution, `Lost`, or `EntropyExhausted` respectively. Invalid entropy is
never reinterpreted as lost probability. A missing ticket stops immediately;
there is no resampling. Timeout remains the independent transition-fuel limit.

**The uniform-index premise is explicit.** Arbitrary replay tokens do not
carry a statistical correctness claim. The OCaml PRNG is an external entropy
provider, not a mathematically verified random source; its statistical quality
is not established by this theorem. The extracted sampler itself exactly
implements the native rational law when supplied uniform bounded indices.
For a sequential-program probability claim, each index must be uniform
conditional on the preceding execution history; uniform marginals alone
would not justify independence of successive samples.

The first implementation materializes the ticket table, using a product
rather than least-common-multiple denominator. It is intended as a simple
verified executable reference, not an efficient sampler for large
denominators. The CLI limits host inputs/resources; this is not a theorem
about host memory, stack use, or performance. Mathematical naturals are kept
inductive during extraction, without unchecked machine-integer substitutions.

## A non-fair partial stateful loop

`Examples/RationalState.v` increments a State counter, then each attempt:

* succeeds with probability `1/3`;
* retries with probability `1/2`;
* loses mass with probability `1/6`.

Its six tickets are `[true,true,false,false,false,missing]`. The loop is
coinductive, not an unrolled finite mockup. It is handled by the existing
State interpreter and executed by the existing fuelled runner.

`extraction/rational-state/` extracts that program, the handler, rational
compiler/selector, and runner. Only CLI and bounded entropy provisioning are
handwritten. The seeded provider copies its input PRNG state before drawing,
so it does not mutate the input state assumed by the pure runner interface.

```
opam exec -- dune exec extraction/rational-state/main.exe -- replay 7 0 2,0,5
# Returned 2 / remaining=1 / consumed=2,0

opam exec -- dune exec extraction/rational-state/main.exe -- replay 100 0 5,0
# Lost / remaining=1 / consumed=5

opam exec -- dune exec extraction/rational-state/main.exe -- seed 1000 0 2026 100
opam exec -- dune exec extraction/rational-state/main.exe -- random 1000 0 100
```

Seed/random modes print the consumed integer trace. Replaying that trace with
the same initial state and fuel reproduces the outcome. The replay's unused
input length need not match the original random provider's unused budget.

## Verification and remaining work

The source gate freezes 361 preceding theory modules and seven preceding
contract snapshots. Twenty-six new compiled contracts cover the compiler,
uniform law, executable boundary, examples, and regressions. Full local build
(including AllImports and both OCaml executables), 19 focused tests, and all
26 compiled contracts passed. The tests actually execute replay, seeded and
random modes and replay recorded draws. Joint three-module `coqchk -norec`
passed, checking selected safe bodies with dependencies trusted; it is not a
whole-library or Gate M audit. CI and environment changes are excluded.

This closes the **single native draw** distribution-correctness gap and adds
random/seed/replay extraction. It does not yet identify the entire finite
runner's returned distribution with a hitting approximant, or prove a
complete program's probability from PRNG runs. That finite execution/semantic
bridge, and an end-to-end verified rewrite example, remain distinct work.
