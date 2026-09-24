# Finite runner probability correspondence

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

`Execution/Backend/UniformReplay.v` gives an explicit `uniform_entropy`
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

`audit_runner_distribution.py` freezes all 365 pre-existing theory sources,
with only four sorted AllImports additions, all prior contract snapshots and
the extraction sources. Its compiled checks require axiom-free finite
operational endpoints and retain the existing logical-axiom whitelist for
the external model adapter. Architecture tests enforce the one-way bridge.
Historical conservation gates consume an explicit additive projection.

The 28-endpoint compiled snapshot distinguishes assumptions: finite execution
and trace-law proofs are closed under the global context. The external-model
bridge inherits existing extensionality and classical description principles;
the arbitrary complete-witness endpoint additionally inherits DS4's
`eq_rect_eq`, constructive definite description and excluded middle. None is
a new probability axiom or an implicit claim of constructive PRNG semantics.

This closes the ideal, conditional finite-distribution and returned-limit
bridge. It does **not** prove PRNG fairness, compiler/runtime correctness,
same-seed or same-fuel peutt congruence, fold/runner correspondence, or an
efficient sampler. Ticket materialization and invalid-versus-exhausted
entropy remain the next execution work; see the [current queue](EFFECTS_EXECUTION.md).

## Local verification

- New modules and the safe `AllImports` aggregate built successfully.
- All 28 new compiled types/assumption contracts passed; old snapshots were
  preserved byte for byte, not regenerated.
- 41 focused tool tests passed: runner distribution (5), architecture (29),
  and the existing extracted State rewrite (7).
- Architecture, source soundness, additive source conservation and diff/link
  checks passed. There are 369 modules, including the unchanged two Gate M files.
- Joint `coqchk -norec` passed for all four new modules, with normal conversion
  and dependencies trusted. This is not a recursive whole-library audit.

An initial checker attempt using native-compute regression casts and VM
fallback hit a Rocq `vmbytegen.ml` assertion; that attempt was not counted as
passing. The new numerical regressions were rewritten using direct definitional
proofs, rebuilt and checked successfully **without** enabling VM conversion.
No environment or checker-policy change was made. The full historical tool
suite and CI were not rerun.
