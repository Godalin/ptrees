# Prove a sampler, extract it, and simulate without fuel

Initial baseline: `ac52a86`; factory follow-up baseline: `ec837bb`.
This is an executable demonstration, **not a new
end-to-end extraction correctness theorem**. All maintained `theories/`
sources, existing contract snapshots, and both old extraction targets are
unchanged. CI and environment changes are out of scope.

## The proved program is the executable program

The example reuses these existing definitions in
`Examples/BernoulliFactory/VonNeumannUnbounded.v`:

* `von_neumann_third`: repeatedly toss a biased coin twice; equal results
  retry, unequal results return the first bit. Each toss is false with
  probability 1/3 and true with probability 2/3.
* `direct_fair`: one direct, fair Boolean sample.

`OperationalVonNeumann.peutt_von_neumann_raw_direct` already proves these
two exact trees equivalent at their complete stable-hitting limits under
the observable FreeOmega interpretation. The old example also establishes
almost-sure termination; it does **not** assert termination on every random
input stream. An infinite sequence of equal pairs keeps retrying.

`extraction/unbounded/Extract.v.in` imports that theorem, checks the proof
reference `program_correct`, and extracts **those same two definitions**.
The OCaml driver does not reimplement either sampling algorithm. Proofs
are erased by extraction; they are not used as a runtime algorithm.

This historical example uses `EnumQ`, which permits mass greater than one.
The small execution adapter checks `mass <= 1`, wraps the unchanged entries
as `SubEnumQ`, and calls the existing exact `ticket_sample`. Overweight
measures are execution errors. No normalization, representation migration,
or change to the theorem's native backend is involved.

## Run it

```sh
opam exec -- dune build extraction/unbounded/main.exe

# One run, with no transition fuel and no entropy budget:
opam exec -- dune exec extraction/unbounded/main.exe -- vn sample 42
opam exec -- dune exec extraction/unbounded/main.exe -- vn random

# Independent statistical experiments on the two proved-equivalent programs:
opam exec -- dune exec extraction/unbounded/main.exe -- vn stats 10000 42
opam exec -- dune exec extraction/unbounded/main.exe -- direct stats 10000 42
```

`stats TRIALS SEED` bounds the **number of requested samples**, not the
execution length of any sample. A divergent sample can prevent the whole
experiment from finishing. `stats-random TRIALS` uses a self-initialized
host PRNG. Repeated trials advance the PRNG; they do not reset it to the
same seed each time.

Observed locally with seed 42:

| Program | Trials | true | false | lost | Native draws |
| --- | ---: | ---: | ---: | ---: | ---: |
| `vn` | 10,000 | 5,063 | 4,937 | 0 | 45,260 |
| `direct` | 10,000 | 4,960 | 5,040 | 0 | 10,000 |

The mathematical target is true=1/2, false=1/2, lost=0. These numbers are
empirical observations, **not a proof of that target**. Equal distributions
do not imply equal outputs or draw counts for a shared PRNG seed. Exact
seed output is not promised across OCaml runtime versions.

## Execution and replay

The generated tree uses OCaml `Lazy.t`. An extracted, total `machine_step`
observes one node, samples at most once, and either supplies the residual
tree or stops. A small handwritten tail-recursive loop schedules those
steps, without fuel. It never restarts the original tree with increasing
fuel and never retries missing mass.

```sh
# One equal pair retries, then false/true returns false; final ticket unused:
opam exec -- dune exec extraction/unbounded/main.exe -- vn replay 0,0,0,3,8
# Returned false; draws=4; remaining=1

# Optional trace is streamed to a NEW file; existing files are not overwritten:
opam exec -- dune exec extraction/unbounded/main.exe -- vn sample 42 --trace /tmp/ptree-vn-new.trace
opam exec -- dune exec extraction/unbounded/main.exe -- vn replay-file /tmp/ptree-vn-new.trace
```

Trace lines are `BOUND TICKET`. Replay checks the requested bound at each
step, so a trace from another sampling layout is rejected rather than
silently reused. A statistics trace concatenates all trials' draws; the
current `replay-file` command replays **one** run (the first trial), not an
entire batch. No trace is retained in RAM by the live random modes.

`steps` counts calls to the single-step machine, including the final Ret
observation. It is diagnostic, not the old runner's fuel convention.

## Bernoulli factory: biased source to a 2/5 target

The same executable now also runs the existing
`BernoulliFactory.third_to_two_fifths` and `direct_two_fifths`:

```sh
opam exec -- dune exec extraction/unbounded/main.exe -- factory stats 10000 42
opam exec -- dune exec extraction/unbounded/main.exe -- factory-direct stats 10000 42
opam exec -- dune exec extraction/unbounded/main.exe -- factory random
opam exec -- dune exec extraction/unbounded/main.exe -- factory replay 0,3,0,3,8
# Returned true; draws=4; remaining=1
```

The implementation nests two unbounded loops:

1. Toss the source coin (false=1/3, true=2/3) until a pair differs, producing
   a fair bit using Von Neumann's method.
2. Feed that bit into the binary rational-coin algorithm, requesting more
   fair bits as needed, starting at target 2/5.

`BernoulliFactoryComposition.peutt_third_to_two_fifths_compositional`
proves the whole factory `peutt`-equivalent to direct Bernoulli(2/5)
sampling. Extraction checks `factory_program_correct` against this existing
compositional theorem and extracts the exact named programs, not a second
implementation. In particular it does **not** use the legacy
`peutt_third_to_two_fifths_direct` endpoint with its extra
`OperationalFactoryStepSupportLaws` premise.

The factory only requests source-coin samples. With the current ticket
compiler every source request has bound 9; the direct target sampler uses
bound 25 (15 false tickets followed by 10 true tickets). Trace tests lock
down this difference: simulation has not replaced the factory by direct
target sampling. Neither loop has a fuel bound.

Observed locally with seed 42:

| Program | Trials | true | false | lost | Native draws |
| --- | ---: | ---: | ---: | ---: | ---: |
| `factory` | 10,000 | 3,908 | 6,092 | 0 | 89,954 |
| `factory-direct` | 10,000 | 4,068 | 5,932 | 0 | 10,000 |

The target is true=2/5, false=3/5, lost=0, **not** the 1/2 target of the
standalone Von Neumann example. All sample/random/replay/trace/statistics
modes and error classifications are shared. As before, frequencies are
empirical; same-seed pointwise equality is neither expected nor promised.
This CLI selects the existing fixed 2/5 instance; it does not yet expose
arbitrary source-bias/target parameters.

`vnE` and `factoryE` are distinct empty event signatures. The extracted
`closed_machine_step` is shared and specialized to each using its empty-event
eliminator. The host packages each correctly typed tree with its step as an
execution closure. It does not cast between signatures, reinterpret Vis,
or change either Rocq program. All maintained theory files remain unchanged.

The compositional theorem's actual compiled signature has no support-law
premise. Its existing logical dependencies are
`RelationalChoice.relational_choice`,
`ClassicalUniqueChoice.dependent_unique_choice`, dependent functional
extensionality, and `Eqdep.Eq_rect_eq.eq_rect_eq`. These are inherited from
the existing proof, not new axioms or a strengthened backend contract added
by this executable follow-up. They differ from the smaller assumption set
of the standalone Von Neumann theorem.

## Boundaries and errors

* `Returned b` is a return; `Lost` is an explicitly sampled missing-mass
  outcome. Statistics divide by **all trials**, including lost trials.
* Divergence stays running. It does not become Lost, Timeout, or a new
  sample. Ctrl-C exits 130 and reports interruption, not a program result.
* Exhausted replay, invalid tickets, malformed/bound-mismatched traces,
  overweight measures and host resource errors exit nonzero. They are not
  recorded as lost probability mass.
* The host retains a 100,000 limit on finite ticket bounds, **not on
  execution length**. Mathematical naturals remain inductive; they are
  not remapped to unchecked machine integers. The existing ticket compiler
  materializes a product-of-denominators table, so large rational measures
  can still be impractical before the host bound check. Efficient sampling
  refinement remains separate work.
* Old bounded runners remain available for finite observation, testing,
  and the existing finite-distribution/hitting theorems. The new host loop
  has not been proved equivalent to them.

The trusted execution boundary includes Rocq extraction, the OCaml runtime,
the PRNG, and the handwritten scheduler/CLI. No fairness theorem for
`Random.State`, OCaml path-distribution theorem, checker relaxation, or
extraction override is introduced. Extraction reports its usual access to
opaque MathComp infrastructure; this is not a new axiom or permission to
disable universe/guard checking. The defensible claim is:

> The Rocq probability program is proved equivalent to direct fair sampling;
> its extracted implementation is supplied for simulation.

## Local checks

```sh
opam exec -- python3 -m unittest discover -s tools -p test_unbounded_execution.py -v
opam exec -- python3 tools/audit_runner_distribution.py
opam exec -- python3 tools/audit_architecture.py --check
```

Local full `dune build`, the 13 new runtime/source tests, the 5 existing
finite-runner-bridge tests, architecture checking, finite-bridge conservation,
soundness source checking and `git diff --check` passed. The mainline remains
369 modules: 367 Gate S and the same 2 isolated Gate M modules. No new
maintained theory module or contract snapshot was needed for the host demo.

The original 13 focused tests exercise both fair outcomes, retry followed by return,
2,000 consecutive retries, unused entropy, streamed replay, error rejection,
explicit and partial missing mass, seed reproducibility, random mode,
and interruption of pure Tau divergence. They also check the actual extracted
root names, lazy representation, absence of extraction overrides/unrealized
axioms, and byte conservation of the old theory, extraction targets, and
contract snapshots. `partial` has true mass 1/2 and lost mass 1/2 and is used
to catch accidental conditional normalization. `lost`, `spin`, `ret`, and
`overweight` are likewise runtime boundary fixtures, not additional results
of the Von Neumann equivalence theorem.

The factory follow-up expands that suite to 18 tests. The five additions
check the compositional theorem/extraction roots, both target outcomes and
the exact direct ticket boundary, 1,000 inner retries followed by 200 full
outer binary cycles, replay exhaustion without fake loss, the 2/5 statistical
target, source-only native draws, streamed replay, and live random mode.
The full local build and 18-test suite pass; architecture and soundness
source audits still report the unchanged 369-module theory. The compiled
factory theorem type and assumptions were queried independently.

The existing theorem's compiled signature was rechecked: it relates exactly
`von_neumann_third` and `direct_fair`, with Boolean equality, using the
observable FreeOmega instances over EnumQ. `Print Assumptions` reports the
existing dependent functional extensionality and `eq_rect_eq` assumptions;
this increment neither removes nor adds to them.

No new whole-library kernel audit, PRNG certification, remote CI claim,
or historical full regression rerun is made for this executable-only step.

## Next work, not required for this demonstration

An efficient rational sampler can refine the current exact ticket sampler
without changing the proved program. Formal correspondence of the new host
loop to finite operational paths is optional strengthening, not a prerequisite
for using these simulations. More proved program/direct-sampling pairs can
be added without redesigning the probability semantics.
