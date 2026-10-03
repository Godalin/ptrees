# Execution and its correctness boundary

Generic interpretation is `fold(handle, sample)` into a target MonadIter:
Vis calls `handle`, Prob calls `sample`. [`Core/Fold`](../theories/Core/Fold.v)
is the main abstraction; the runner is a concrete closed-tree execution route,
not an alternative canonical probability semantics. Lawful fold targets and
transformer agreements are described in [Interpreters](INTERPRETERS.md).
When a target selects `MonadSample MN T`, `interpM handle` is definitionally
this same fold with `msample`; selection does not certify the sampler's law.

## Closed execution

`Execution/Runner` accepts a closed `ptree void1 MN A` and a deterministic
sampler. Eliminate external effects with interp/fold first, or fold directly
to an ITree/IO target; the runner does not duplicate the handler calculus.

| Outcome | Meaning |
| --- | --- |
| `Returned a` | Program result |
| `Lost` | A native subprobability draw encountered missing mass |
| `Timeout` | Bounded runner exhausted transition fuel |
| `EntropyExhausted` | Replay/source failure, including invalid supplied entropy |

The result/failure API distinguishes the first two from runner artifacts;
`finished` admits only Returned/Lost. The fuel-free `executes` relation is the
operational account, related to finished executions at sufficiently large fuel.
`run fuel` is an executable approximation. Divergence is neither Lost nor
EntropyExhausted; Timeout is not part of core PTree semantics.

## Exact rational sampling

The SubEnumQ ticket compiler uses a product of denominators `d`, represents
each entry by exactly `p*d` value tickets, and fills the remaining slots with
missing tickets. There are exactly `d` tickets even for the empty distribution.
No floating point, normalization, sorting or deduplication is involved.

`compile_tickets_expectation` and `uniform_ticket_expectation` prove the
finite rational law for arbitrary signed tests, including:

```text
E[f(draw_ticket mu i)]
 = expect_mu (fun x => f(Some x)) + (1 - mass mu) * f(None)
```

Here `i` must be uniform on `[0,d)`. `ticket_sample` validates the supplied
index; missing or invalid entropy is not reinterpreted as lost mass.
Missing tickets stop execution rather than resampling. This is a reference
sampler, not an efficient algorithm for large denominators.

## Actual bounded runner to complete hitting

`Execution/Backend/FiniteDistribution` defines an ideal total outcome law:
Ret uses no fuel; Tau and Prob each consume one; Prob adds explicit Lost mass;
unresolved work at zero fuel becomes Timeout. EntropyExhausted has zero mass
in this ideal law. The probabilities of Returned, Lost and Timeout sum to one.

`Execution/Validation/UniformReplay` defines a history-conditional uniformity
predicate and constructs a source satisfying it. `finite_runner_distribution`
proves the law of the **actual** `run + ticket_replay` for arbitrary rational
outcome tests. Uniform marginals alone are insufficient: each draw must be
uniform conditional on the preceding history and requested bound.

`Execution/Validation/SubEnumQ` then proves:

```text
actual bounded replay expectation
  = finite outcome expectation
  = returned projection of hitting approximation n
  -- supremum over n --> complete stable-hitting expectation
```

`finite_runner_hitting` uses exactly the same fuel `n`, not a cofinal shift.
`replay_hitting_limit` and `runner_stable_hitting_adequacy` give the limit for
bounded rational return tests and any complete hitting witness. The projection
forgets Lost/Timeout; finite Lost probability is **not** total missing hitting
mass, which can also contain divergence. These adapters are one-way external
validation and are not imported by ordinary execution or extracted.

## Fuel-free OCaml simulation

The unbounded executable extracts the same proved VN/factory programs and an
individual machine step. A handwritten tail-recursive scheduler runs steps
until Returned/Lost. A divergent run can run forever, even when the program
terminates almost surely under its mathematical distribution.

```sh
opam exec -- dune build extraction/unbounded/main.exe
opam exec -- dune exec extraction/unbounded/main.exe -- vn sample 42
opam exec -- dune exec extraction/unbounded/main.exe -- vn stats 10000 42
opam exec -- dune exec extraction/unbounded/main.exe -- direct stats 10000 42
opam exec -- dune exec extraction/unbounded/main.exe -- factory stats 10000 42
opam exec -- dune exec extraction/unbounded/main.exe -- factory-direct stats 10000 42
opam exec -- dune exec extraction/unbounded/main.exe -- factory replay 0,3,0,3,8
```

VN is proved equivalent to a fair draw; the nested factory is proved equivalent
to Bernoulli(2/5) by the existing compositional theorem. The CLI selects that
fixed instance; it does not expose the theorem's arbitrary rational parameters.
The legacy EnumQ programs use an execution adapter checking `mass <= 1` before
ticket sampling, not normalization or an unchecked weighted sampler.

`stats` limits the requested number of trials, not each trial's execution
length. Frequencies use all trials, including lost ones. Same distribution
does not imply same-seed outputs, draw counts or finite-fuel observations.

Replay-file lines are `BOUND TICKET`; mismatched bounds are errors. A trace
from a batch records successive trials, while replay-file replays one run.
Use a fresh `--trace` path: existing files are not overwritten. Invalid input,
exhausted replay and resource errors exit nonzero, not as missing probability;
interruption is not a program outcome. Mathematical naturals are not replaced
by unchecked machine integers. Ticket-table size remains a practical limit.

## What is and is not proved

Every finite execution horizon is linked to the mathematical hitting
approximants under the explicit ideal entropy law. Its supremum matches
complete hitting. Separately, extracted coinductive programs support fuel-free
experiments. The OCaml PRNG, handwritten scheduler and full extraction/runtime
pipeline have no end-to-end probability correctness theorem; neither arbitrary
replay files nor empirical frequencies are proofs.

The existing executable demonstrations also include State rewriting, a partial
rational loop and the interactive factory controller. Their roots and main
equational results are linked in [Case studies](CASE_STUDIES.md).
Run `python3 -m unittest discover -s tools -p test_execution.py` after building;
use the rational-ticket, runner-distribution and effect-execution contract
groups through [Maintained verification](AUDITING.md).
