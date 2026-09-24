# End-to-end State + probability case study

Baseline: `60e1e77`. `Examples/StateRewrite.v` is an application of existing
theory, not a new backend theorem or interpreter definition.

## One proof chain

The original program reads State, draws a fair Boolean, and then makes a
second native draw whose distribution depends on that Boolean. It updates
State according to the result, and enters the existing unbounded rational
attempt loop. The second distribution can have missing mass.

The rewritten program replaces the consecutive sampling nodes by their
native Kleisli composition. Everything else, including the unbounded
continuation and State operations, is unchanged:

```
Prob coin (fun b => Prob (preparation_coin b) k)
             ≈ₚ
Prob (subenumQ_bind coin preparation_coin) k
```

The proof has three small steps:

1. `preparation_sampling_fusion` applies the existing generic
   `peutt_prob_flatten` (with the native interpretation supplied explicitly).
2. `source_program_rewrite` places that result under the original Get event.
3. `rewrite_then_handle` applies the already-proved State preservation
   theorem, obtaining canonical `≈ₚ` between the resulting closed trees.

There is no new coinduction, sampling axiom, global inference hint, or
FreeOmega-specific fusion proof. The program uses the actual canonical
behavioral route. The completion State endpoint is just the existing thin
client of the generic State theorem.

The fused preparation returns true with mass `1/6`, false with `3/4`, and
loses `1/12`. These values are checked against the verified uniform-ticket
expectation. Missing mass is not normalized away by the algebra or runner.

## Extract both proof-linked programs

The rational executable now has optional `original` and `rewrite` prefixes.
Its previous unprefixed counter mode is unchanged. Both new roots execute
the actual programs occurring in the equivalence theorem, through the same
extracted State handler, rational sampler and runner:

```
opam exec -- dune exec extraction/rational-state/main.exe -- original replay 7 0 2,0,0
# Returned 11 / remaining=0 / consumed=2,0,0

opam exec -- dune exec extraction/rational-state/main.exe -- rewrite replay 6 0 24,0
# Returned 11 / remaining=0 / consumed=24,0

opam exec -- dune exec extraction/rational-state/main.exe -- rewrite seed 1000 0 2026 100
opam exec -- dune exec extraction/rational-state/main.exe -- rewrite random 1000 0 100
```

`rewritten_trace_has_operational_path` invokes the verified runner's
`run_sound` theorem on the actual rewritten program and trace. Thus the
concrete returned result is linked to the Coq operational execution relation,
not merely to an OCaml output string.

## What equivalence does not say

Fusion removes one Prob node. It changes the number and bounds of requested
random integers, and consumes one fewer unit of transition fuel. Therefore
the claim is **probabilistic behavioral equality**, not equality of arbitrary
replay traces, seeds, or finite-fuel outcomes across the two programs.

`original_needs_an_extra_transition` and the executable tests deliberately
show that at fuel 6 the corresponding original trace times out while the
rewritten trace returns. Each program separately replays its own recorded
seeded execution. Tests do not incorrectly require identical traces or
outcomes under the same PRNG seed across the rewrite.

## Current roadmap boundary

The effects/execution chain now includes arbitrary fixed-handler weak
preservation, stateful weak preservation, standard Reader/Writer/Exception
clients, generic separate-algebra fold, StateT commutation in a lawful target,
finite runner/path equivalence, exact rational single-draw probability, and
extracted random/seed/replay execution of a proved rewrite.

The proposal's stronger identification of **the full finite-runner outcome
distribution with hitting approximants** was not proved at this checkpoint.
The subsequent [runner probability bridge](RUNNER_DISTRIBUTION.md) proves the
finite outcome law and returned hitting correspondence under conditional
uniform entropy. No PRNG fairness proof or same-fuel peutt congruence is claimed.
The generic-eventless-iteration/Atomic/MDP cleanup items are separate theory
work, not silently reported as completed by this execution increment.

Source conservation freezes the preceding 364 theory modules and eight
contract snapshots. Thirteen new compiled contracts cover the proof chain,
operational witness, exact preparation masses and executable boundaries.

The three proof-chain endpoints inherit
`RelationalChoice.relational_choice` and
`ClassicalUniqueChoice.dependent_unique_choice` from the existing
`PTree.Eq.PEutt.peutt_prob_flatten`. These assumptions are already recorded
for that exact theorem in the frozen mainline contract. The client audit
permits only that frozen inheritance, alongside the existing extensionality
dependencies of the completion/State specialization; it does **not** expand
the Domain/sampler axiom whitelist. The newly written rational sampler remains
axiom-free. No new semantic axiom is introduced and the example is not
misreported as closed under the global context.

Local validation passed: full build/AllImports and extraction, 65 focused
effect/execution tool tests, 13 new compiled contracts, 26 unchanged rational
sampler contracts, and all 465 unchanged mainline compiled contracts.
Architecture and soundness source audits passed. Targeted `coqchk -norec`
checked the example body (trusting dependencies), not a recursive whole-library
or Gate M audit. No CI or environment changes.
