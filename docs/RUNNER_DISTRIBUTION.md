# Finite runner probability correspondence

Current ownership: replay probability laws live in
`Execution/Validation/UniformReplay.v`, separate from executable samplers in
`Execution/Backend`. The move preserves every definition and proof; there is
no old-path forwarding module. The runner now offers a typed result/failure
view without changing its runtime representation. See the
[execution role map](EFFECTS_EXECUTION.md#execution-roles-and-public-terminology).
The baseline and verification counts below describe the original increment.

Baseline: `892a6d3`. Four additive theory modules connect the existing runner
and rational ticket implementation to the existing mathematical hitting
semantics. No sampler, runtime, PRNG, native backend, FreeOmega or PTree
relation definition is changed. CI and environment changes are excluded.

## Exact finite outcome law

`Execution/Backend/FiniteDistribution.v` defines a finite rational list of
outcomes for a closed `ptree void1 SubEnumQ A`:

- Ret returns immediately, even with zero fuel.
- Tau spends one unit; with zero fuel it yields Timeout.
- Prob spends one unit, weights each continuation by its original native
  coefficient, and adds an explicit Lost outcome of weight `1 - mass mu`.
- Prob with zero fuel yields Timeout without requesting a draw.

The list has nonnegative weights and total mass exactly one. Duplicate entries
are permitted. `EntropyExhausted` has zero probability in this ideal law.
`outcome_expectation` accepts arbitrary signed rational tests on **all**
outcomes, so the statement is not merely a return-probability calculation.

## History-conditional sampling and the actual runner

`Execution/Validation/UniformReplay.v` gives an explicit `uniform_entropy`
predicate, not a class or an axiom. A source maps the prior reversed ticket
history and the newly requested bound to a finite rational law of indices.
At every history and positive bound its weights must be nonnegative and its
expectation must equal the uniform law on `[0,bound)` for every rational test.
`fresh_uniform_entropy` constructs a source satisfying the predicate.

`trace_distribution` composes those conditional laws along the finite program.
Bounds can change from branch to branch; Lost stops rather than resampling;
Ret and Timeout request no further entropy. The generated trace law is itself
nonnegative and has mass one. It is an ideal finite experiment, **not** a law
proved for `Random.State`, a fixed seed, or an arbitrary replay file.

The main theorem is:

```text
uniform_entropy source
  => E[ f(fst(run ticket_replay fuel t trace))
         | trace drawn from trace_distribution source fuel t history ]
     = outcome_expectation fuel t f
```

This is `finite_runner_distribution`. The left side calls the **existing**
`run` and `ticket_replay`, not another implementation of their control flow.
The proof is induction on fuel using the existing
`uniform_ticket_expectation` for each history-dependent draw. Ret/Tau/Prob
and entropy validation keep their original implementations. The finite
operational theorems are closed under the global context.

## Same-fuel hitting and the limit

`Execution/Validation/SubEnumQ.v` is a one-way external validation adapter.
Its imports may include execution, the independent OmegaVal model and DS4.
Ordinary execution and maintained reasoning modules may not import it, even
indirectly. The adapter is not extracted.

`finite_runner_hitting` proves for every rational return test `f`:

```text
ratr (outcome_expectation n t (Returned-only f))
  = eval (ptree_domain_approx n (observe t)) (FHRet-only (ratr o f))
```

The index is exactly `n`, not `n+1`: both semantics resolve Ret without
internal fuel, while Tau/Prob each consume one unit. Closed trees have no Vis
case. `replay_hitting` composes this with the actual replay theorem.

`replay_hitting_limit` then identifies the supremum of finite returned
expectations with mathematical complete hitting. Finally,
`runner_stable_hitting_adequacy` uses existing DS4 adequacy to obtain that
same supremum from **any complete FreeOmega hitting witness**, for bounded
rational tests. Such tests include Boolean event indicators. This does not
claim an arbitrary-real-observable runtime theorem or add another completion.

The projection forgets Lost and Timeout. These are different reasons for
absent return mass: explicit missing mass can be encountered at a finite
draw; divergence manifests as continuing Timeout at every finite horizon.
No theorem equates finite Lost probability with total missing hitting mass.

## Checked boundaries

The regression exercises a genuinely unbounded retry tree, with each attempt
returning with probability `1/3`, retrying with `1/2`, and losing `1/6`:

| Fuel | Returned | Lost | Timeout |
| --- | --- | --- | --- |
| 1 | 1/3 | 1/6 | 1/2 |
| 3 | 1/2 | 1/4 | 1/4 |

It checks the second result through the actual replay-distribution theorem,
plus the eliminated State counter, arbitrary-fuel hitting and the unbounded
limit. A type-valued result carrier checks the higher-universe client. Other checks cover
zero-fuel Ret, no entropy at a timed-out Prob, pure Tau divergence versus
immediate zero-mass loss, and rejection of biased/history-correlated entropy.
Import probes ensure the finite execution layer does not load Domain,
FreeOmega or peutt before the explicit validation import.

## Audit and remaining boundary

The maintained `runner_distribution` group checks finite operational and
external-model endpoints in their declared trust context. Architecture checks
enforce the one-way validation bridge.

The 28-endpoint compiled snapshot distinguishes assumptions: finite execution
and trace-law proofs are closed under the global context. The external-model
bridge inherits existing extensionality and classical description principles;
the arbitrary complete-witness endpoint additionally inherits DS4's
`eq_rect_eq`, constructive definite description and excluded middle. None is
a new probability axiom or an implicit claim of constructive PRNG semantics.

This closes the ideal, conditional finite-distribution and returned-limit
bridge. It does **not** prove PRNG fairness, compiler/runtime correctness,
same-seed or same-fuel peutt congruence, fold/runner correspondence, or an
efficient sampler. See the [execution guide](EFFECTS_EXECUTION.md) for the
current implementation, failure terminology and follow-up scope.

## Current verification

These are focused checks of the current compiled types and logical assumptions:

```sh
python3 tools/audit_contracts.py --group runner_distribution
```

Build first with `opam exec -- dune build`. For architecture, source safety,
all registered groups, runtime tests and the separately scoped kernel check,
use [Maintained verification](AUDITING.md). Gate M checks are isolated and do
not constitute universe-checked evidence. Local checks do not assert CI passed.
The retired stage-specific source-replay scripts and their historical
module/test counts remain in Git; they are not current-tree invariants.
