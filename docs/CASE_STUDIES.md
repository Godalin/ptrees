# Reasoning with PTree: a case-study guide

Start with the program you want to prove, not the implementation of the
probability model. The gallery is broader than the paper's eventual selection.
The [case-study standard](CASE_STUDY_STANDARD.md) governs presentation, not
which proof method a case is allowed to use.

## Choose a starting point

- **Replace a local computation inside a larger program:** algebraic rewriting.
  Start with StateRewrite, then BernoulliFactoryComposition and FactoryController.
- **Analyze an unbounded loop from its complete one-round behavior:** frontier
  iteration. Start with IterationBasics, then AbsorbingFrontier. Read RandomWalk
  for the analysis that a general iteration theorem does not do for you.
- **Relate persistent interaction while maintaining a recursive relation:**
  coinduction up to bind or coupled Prob. Start with InteractiveVonNeumannService,
  then MixedHeadProtocol.
- **All three occur:** normalize local computations, summarize loops, prove a
  component endpoint, then compose it into the outer protocol. AdaptiveFactoryController
  is the integrated example, not the introductory tutorial.

These are complementary tools, not mutually exclusive proof modes. Rewriting
handles algebraic transformations; it does not replace convergence analysis,
coupling certificates or protocol invariants.

## Reading entries and reusable results

Paths below are relative to `theories/Examples`. Each linked file identifies
its concrete backend at setup; program calculations consume the selected
semantic algebra rather than repeatedly opening its finite-list representation.

| Case | Read first | Further endpoints / boundaries |
|---|---|---|
| [StateRewrite](../theories/Examples/StateRewrite.v) | `source_program_rewrite`, `rewrite_then_handle` | State interpretation and concrete execution hooks. Equal behavior is not same-fuel or same-entropy execution. |
| [IterationBasics](../theories/Examples/IterationBasics.v) | `IterationBasics.loop_frontier_exact`, `loop_classical` | `loop_probability`, `endless_frontier_zero`: returns of mass 1, 1/2 and 0. No AST premise. |
| [BernoulliFactoryComposition](../theories/Examples/BernoulliFactory/BernoulliFactoryComposition.v) | `peutt_factory_correct`, `peutt_factory_vn_direct` | Reuses sampler endpoints under bind/iteration; shared arithmetic remains in its analysis owners. |
| [AbsorbingFrontier](../theories/Examples/AbsorbingFrontier.v) | `absorbing_program_rewrite`, `absorbing_generic_frontier` | `absorbing_generic_frontier_reference` joins algebraic and exact-frontier views by whole-head lifting. `offer_probability` is 1/2. |
| [InteractiveVonNeumannService](../theories/Examples/InteractiveVonNeumann/InteractiveVonNeumannService.v) | `interactive_von_neumann_service_equivalent` | Up-to-bind consumes `service_sampler_equivalent`. `von_neumann_request_true_reply_trace_probability` supplies a quantitative interaction result. |
| [MixedHeadProtocol](../theories/Examples/MixedHeadProtocol.v) | `masked_protocol_equivalent` | Up-to-Prob uses an actual non-diagonal coupling and a recursive invariant. `masked_challenge_true_reply_probability` is quantitative; no execution endpoint is claimed. |
| [FactoryController](../theories/Examples/FactoryController.v) | `Rewriting.factory_controller_program_rewrite` | Full sampler/handler calculation; `Observation.factory_next_action_probability`; concrete scripted/extraction entries. |
| [RandomWalk](../theories/Examples/RandomWalk.v) | `random_walk_as_successive_passages`, `random_walk_closed_form` | Passage normalization, AST and infinite-support output analysis. Not a finite native distribution node. |
| [AdaptiveFactoryController](../theories/Examples/AdaptiveFactoryController.v) | `Adaptive.controller_program_rewrite` | `loop_hits`, `raw_loop_fair`, `adaptive_factory_direct`, `controller_refinement`. Preserve correlated state; no new simulator/PRNG claim. |

Adaptive's programs and canonical behavior use `SubEnumQ -> FreeOmega SubEnumQ`.
Its reusable [bounded factory](../theories/Examples/BernoulliFactory/BoundedFactory.v)
connects the existing finite rational analysis to that bounded backend; raw
`EnumQ` is an analysis representation, not Adaptive's execution carrier.

For effect-specific and executable supporting examples, also see
[ITreeSampling](../theories/Examples/ITreeSampling.v),
[EffectInteractions](../theories/Examples/EffectInteractions.v),
[StateCounter](../theories/Examples/StateCounter.v) and
[RationalState](../theories/Examples/RationalState.v).
Shared VN/rational proofs are dependencies to reuse, not material to copy into
each service. Regression modules are contract/negative tests, not required
imports for examples.

## IterationBasics: what the three versions establish

The tutorial selects `SubEnumQ -> FreeOmega SubEnumQ`. Its inhabited effect
signature permits an Ask event, but the supplied round frontiers contain
only returns. The first two share the same Tau/sample/iter program; the third
uses an unconditional retry round:

| Round | Retry | Return true | Missing mass | Eventual return mass |
|---|---:|---:|---:|---:|
| Geometric | 1/2 | 1/2 | 0 | 1 |
| Partial | 1/2 | 1/4 | 1/4 | 1/2 |
| Endless | 1 | 0 | 0 | 0 |

The last two have different causes of absent return mass: native loss versus
endless internal execution. Neither is conditional normalization. A complete
summary exists in each case, so summary existence is not a termination proof.

The program/frontier proof and finite numerical analysis are separate:

```text
one-round certificate → generic complete frontier → classical mixed_iter
finite expectation recurrence → geometric decay → selected observation law
```

`rows_expect` proves the finite return mass is
`return_mass * (1 - (1/2)^n)` for the first two versions. `geometric_ast`
additionally certifies total hitting for the geometric version. The endless
version has the exact zero frontier and zero observation, not a claim that
all of its finite rounds fail to finish (each round returns a retry).

The generic complete-frontier representative and the observation convenience's
representative are explicitly compared by `two_frontiers_agree`; different
formal syntax is not a different loop semantics. Finite frontier rounds are
one ahead of bottom-starting Kleisli approximants; the limit removes this shift.

For genuine order-theoretic leastness, see [ReturnIteration](RETURN_ITERATION.md):
MathComp native iteration and the independent OmegaVal model prove it. The
FreeOmega validation theorem interprets its canonical approximants into that
lfp. Examples do **not** import external validation, and raw FreeOmega's
approximation order is not silently treated as a complete CPO.

## AbsorbingFrontier: two views of the same program

The algebraic route is unchanged:

```text
eventful iter ≈ VN >>= reveal ≈ fair >>= reveal = direct program
```

The semantic route proves an explicit complete frontier of `absorbing_step`
and directly applies generic `iteration_summary_hitting`. Retry, Ret and Vis
occur together. The visible head retains the actual bind continuation, and
iteration wraps it with the actual residual recursive program. Even eliminating
a return/bind redex is not literal coinductive-tree equality.

`absorbing_generic_frontier_reference` connects that exact witness to the
simple fair Ret/Vis reference using whole-continuation lifting. It does not
replace actual continuations by behavioral equivalents inside an exact witness.

## Capabilities and honest boundaries

The gallery demonstrates established proof principles **under their theorem
premises**, not unconditional support by every backend. In particular:

- Direct relational iteration additionally needs relational limit closure;
  generic frontier adequacy does not have the same premise list.
- MathComp direct retains its explicit mathematical conditions and isolated
  Gate M universe relaxation. None of this gallery work expands Gate M.
- AST and quantitative closed forms require actual probability analysis;
  neither follows from summary existence alone.
- Adaptive's native summary handles a special *kind of problem* covered by
  generic frontier iteration. Its current convenience implementation still
  uses behavioral iteration and primitive-loop cofinality; it is not claimed
  to call `FrontierIteration` directly. Its bit-only observation avoids asking
  for a finite native state/bit joint limit.
- Finite observations, external mathematical validation and extracted
  experiments remain different endpoints. Host randomness is not thereby
  formally verified.

No new context closure, probability class, facade or operator is needed for
this learning path. A concrete blocked client, not backend symmetry or proof
line count, should motivate the next foundational extension.
