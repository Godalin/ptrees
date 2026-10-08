# Reasoning with PTree: a case-study guide

Start with the program you want to prove, not the implementation of the
probability model. The gallery is broader than the paper's two principal cases:
Adaptive and pGCL/RandomWalk. FactoryController supports execution and algebra;
MixedHead supports the appendix's coupling/coinduction discussion.
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
  then MixedHead.
- **All three occur:** normalize local computations, summarize loops, prove a
  component endpoint, then compose it into the outer protocol. AdaptiveFactoryController
  is the integrated example, not the introductory tutorial.

These are complementary tools, not mutually exclusive proof modes. Rewriting
handles algebraic transformations; it does not replace convergence analysis,
coupling certificates or protocol invariants.

## Paper theorem index

This index follows the current manuscript's §2/§9.1 (Adaptive), §5.4/§9.2
(iteration and RandomWalk), and supporting appendices. Names below are
qualified relative to `PTree.Examples`; the linked source owns the statement.
Program hypotheses and logical assumptions are different: the former appear
in theorem types; the latter are recorded by the
[compiled contracts](../tools/data/CONTRACT_SUITES.json) and explained in the
[assumption guide](AUDITING.md#logical-assumptions-and-their-roles).

| Paper role | Source endpoint | Hypotheses / meaning |
|---|---|---|
| Adaptive refinement | [`AdaptiveFactoryController.Adaptive.controller_refinement`](../theories/Examples/AdaptiveFactoryController.v) | Any initial private state, rational `0 ≤ q ≤ 1`; the two fixed source biases and concrete handler are definitions. Heterogeneous `state_result` hides state, not state/bit correlation. |
| Adaptive calculation | `AdaptiveFactoryController.Adaptive.controller_program_rewrite` | Same parameters; the complete projected program calculation, not a call to the final refinement theorem. Uses `adaptive_factory_direct`, ultimately `raw_loop_fair`. |
| Forward language semantics | [`PGCL.Forward.denote_spec`, `denote_while_unfold`](../theories/Examples/PGCL/Forward.v) | Backend-parametric kernel semantics; selected limits and algebra use the explicit probability profiles in their sections. No PTree or external model is needed to define `denotes`. |
| Interpretation correspondence | [`PGCL.FreeOmega.pgcl_run_hitting`, `pgcl_run_denotes_iff`](../theories/Examples/PGCL/FreeOmega.v) | The native core/AE/countable-AE profile instantiates generic adequacy with observable FreeOmega. Exact return frontiers of State-interpreted programs, not merely one expectation. |
| While leastness | `PGCL.FreeOmega.pgcl_while_least_fixed_point` | The native profile in `WhileOrder`; a quotient fixed-point equation and leastness among `⊑ω`-prefixed kernels. Neither AST nor an external model is a premise; arbitrary semantic-chain completeness is not claimed. |
| RandomWalk instance | [`PGCL.RandomWalk.walk_source`, `walk_denote_least_fixed_point`, `walk_run`, `walk_classical_frontier`](../theories/Examples/PGCL/RandomWalk.v) | The source uses the fixed `2/3` coin. Its forward lfp is the complete return frontier of the interpreted and previously analysed PTree programs. |
| Quantitative result | `PGCL.RandomWalk.walk_denote_closed_form` | Limit representation, finite-round observations, atomwise probability limits and normalization. The final infinite-support law is not a finite native sample. |

For the concrete endpoints, `raw_loop_fair` and
`walk_denote_least_fixed_point` currently use functional extensionality;
`adaptive_factory_direct`, `controller_program_rewrite`, `controller_refinement`
and `walk_forward` additionally inherit relational/dependent unique choice.
`walk_denote_closed_form` is closed under the global context. None of these
endpoints uses UIP or Gate M. These are audited dependencies of the current
proofs, not claims that the assumptions are necessary.

**Manuscript synchronization, not missing theory.** The read-only review of
the sibling manuscript at `bfb14d4` found three remaining updates: §5.4 should distinguish internal
FreeOmega `⊑ω` leastness from external validation; §9.2 and Appendix F's
RandomWalk mapping should include the pGCL source/forward-semantics chain;
§10 and Appendix F should replace the old raw-EnumQ FactoryController execution
description with SubEnumQ. The simulator still has an unverified textual parser,
host PRNG and fuel-free scheduler, and its integer store has no proved
representation bridge to the pair-state RandomWalk. No manuscript file is
maintained by this index.

For the core theory behind these cases, follow
[stable observations](THEORY.md#relations-and-stable-observations),
[program algebra](THEORY.md#bind-and-rewriting) and
[up-to rules](THEORY.md#coinduction-up-to-contexts), rather than backend proof
internals. MixedHead's alternative proof below is appendix material, not a
second principal case or a second special-purpose up-to technique.

## Reading entries and reusable results

Paths below are relative to `theories/Examples`. Each linked file identifies
its concrete backend at setup; program calculations consume the selected
semantic algebra rather than repeatedly opening its finite-list representation.

At the finite-backend construction boundary, import
`Prob.Backend.Common.FiniteSubdist` and use the opt-in `finite_distribution`
tactic. The target type selects `SubEnumQ` or `SubEnumR R`; no new semantic
typeclass or `distₘ` notation is involved. For example:

```coq
Definition uniform3 : SubEnumQ hidden3.
Proof. finite_distribution [:: (1/3, L0); (1/3, L1); (1/3, L2)]. Defined.
```

Closed rational weights are checked by computation. Symbolic/real weights
leave scalar nonnegativity and mass inequalities for the caller, not
list-membership proofs. The shared `finite_subdist_checked` constructor
preserves the exact list and its expectations: no normalization, pruning,
reordering or duplicate merging. Total mass may be less than one; invalid
weights cannot produce a completed definition without a validity proof.
This is finite representation infrastructure, not a construction operation
assumed of every `SemanticMeasure`.

Examples use this constructor for bounded list literals, including partial
and duplicate-weight distributions and the polymorphic pGCL Bernoulli coin.
An existing `EnumQ` analysis object is still embedded with `enumQ_as_subprob`:
that bridge preserves the original object rather than reconstructing its list.

| Case | Read first | Further endpoints / boundaries |
|---|---|---|
| [StateRewrite](../theories/Examples/StateRewrite.v) | `source_program_rewrite`, `rewrite_then_handle` | State interpretation and concrete execution hooks. Equal behavior is not same-fuel or same-entropy execution. |
| [IterationBasics](../theories/Examples/IterationBasics.v) | `IterationBasics.loop_frontier_exact`, `loop_classical` | `loop_probability`, `endless_frontier_zero`: returns of mass 1, 1/2 and 0. No AST premise. |
| [pGCL](../theories/Examples/PGCL/Programs.v) | `FreeOmega.pgcl_run_denotes_iff`, `FreeOmega.pgcl_while_least_fixed_point`, `Runtime.Adequacy.compile_hitting` | State-effect elaboration, generic forward kernels and Q/R instances; FreeOmega while leastness under `⊑ω`. [Runtime-input simulator](EXECUTION.md#a-runtime-input-pgcl-simulator) uses the checked frontend; parser and host randomness are not verified. [Semantic scope](ITERATION.md#pgcl-forward-semantics-no-wp-or-external-model): no wp or external validation. |
| [BernoulliFactoryComposition](../theories/Examples/BernoulliFactory/BernoulliFactoryComposition.v) | `peutt_factory_correct`, `peutt_factory_vn_direct` | Reuses sampler endpoints under bind/iteration; shared arithmetic remains in its analysis owners. |
| [AbsorbingFrontier](../theories/Examples/AbsorbingFrontier.v) | `absorbing_program_rewrite`, `absorbing_generic_frontier` | `absorbing_generic_frontier_reference` joins algebraic and exact-frontier views by whole-head lifting. `offer_probability` is 1/2. |
| [InteractiveVonNeumannService](../theories/Examples/InteractiveVonNeumann/InteractiveVonNeumannService.v) | `interactive_von_neumann_service_equivalent` | Up-to-bind consumes `service_sampler_equivalent`. `von_neumann_request_true_reply_trace_probability` supplies a quantitative interaction result. |
| [MixedHead](../theories/Examples/MixedHead/Protocol.v) | Complete programs (§2), then the in-place compositional proof `masked_protocol_equivalent` (§4), with no bridge premise | A branching Boolean sampler versus a one-shot specification, related through finite stable hitting and up-to-bind. The same non-functional 3-to-2 joint abstracts heterogeneous Ret payloads and recursive Vis continuations. `masked_public_protocol_equivalent` erases the payload; `masked_challenge_true_reply_probability` retains the `3/8` and `1/8` queries. No execution endpoint is claimed. |
| [FactoryController](../theories/Examples/FactoryController.v) | `Rewriting.factory_controller_program_rewrite` | Full sampler/handler calculation; `Observation.factory_next_action_probability`; concrete scripted/extraction entries. |
| [RandomWalk](../theories/Examples/PGCL/RandomWalk.v) | `walk_source`, `walk_denote_least_fixed_point`, `walk_forward`, `walk_denote_closed_form` | pGCL source, classical semantic lfp, exact finite rounds and infinite-support output law. Passage/harmonic proofs are supporting [analysis](../theories/Examples/PGCL/RandomWalkAnalysis.v). The simulator's integer-store walk implements the same transition, without a proved representation bridge to this pair-state case. |
| [AdaptiveFactoryController](../theories/Examples/AdaptiveFactoryController.v) | `Adaptive.controller_refinement`, with its calculation in `controller_program_rewrite` | `lower_attempt_kernel`, `loop_hits`, `raw_loop_fair`, `adaptive_factory_direct`. Preserve correlated state; no new simulator/PRNG claim. |

For an appendix-oriented alternative to MixedHead's in-place proof, read
[`UpTo.v`](../theories/Examples/MixedHead/UpTo.v):
`draw_impl_kernel` verifies the finite sampler, `masked_kernel_equivalent`
uses **coinduction up to bind**, and `kernel_spec_equivalent` uses **ordinary
coinduction with native coupling of complete Ret/Vis frontiers**. Their
composition, `masked_protocol_equivalent_upto`, proves the same public claim
without calling the original `masked_protocol_equivalent`. The original
programs and direct proof are retained unchanged. Prob is not a progress
guard; Challenge/Reply and the stable-hitting generator govern progress.

Adaptive's programs and canonical behavior use `SubEnumQ -> FreeOmega SubEnumQ`.
Its reusable [bounded factory](../theories/Examples/BernoulliFactory/BoundedFactory.v)
connects the existing finite rational analysis to that bounded backend; raw
`EnumQ` is an analysis representation, not Adaptive's execution carrier.

For effect-specific and executable supporting examples, also see
[ITreeSampling](../theories/Examples/ITreeSampling.v),
[EffectInteractions](../theories/Examples/EffectInteractions.v),
[RealSamplingHandler](../theories/Examples/RealSamplingHandler.v),
[StateCounter](../theories/Examples/StateCounter.v) and
[RationalState](../theories/Examples/RationalState.v).
Shared VN/rational proofs are dependencies to reuse, not material to copy into
each service. Technical compilation clients live in the non-installed
`tests/` target; examples do not import them.

## Reading FreeOmega expressions

The tutorials and frontier calculations opt into a small syntax layer:

```coq
Require Import PTree.Prob.FreeOmega.Definition.
Local Open Scope freeomega_scope.
```

| Client notation | Exact expansion / meaning |
|---|---|
| `ηω x` | `FORet x`: return a value in the formal measure |
| `⊥ω` | `FOZero`: the zero expression |
| `x ←ω mu ;; t` | `FOSample mu (fun x => t)`: native sampling |
| `m >>=ω k` | `free_omega_bind m k`: bind of raw FreeOmega expressions |
| `supω n, t` | `FOLub (fun n => t)`: formal countable completion |
| `↑ω mu` | `free_omega_sample mu`, definitionally `FOSample mu FORet` |

Return, zero, native sampling, bind, formal supremum and native embedding share
the `ω` suffix.

The definition module opens no scope for clients; `(expression)%fo` also works without
opening the scope. Native sampling `←ω` is deliberately distinct from program
sequencing `<-`. No typeclass selects a measure interpretation here, and no
equality/lifting relation is redefined. Semantic clients use `>>=ₘ` for bind
on their selected FreeOmega measure instance. Syntax-only proofs use
`>>=ω`: notation does not add native capabilities or require an
observable instance just to manipulate the datatype.

For example, the complete silent-round frontier in IterationBasics reads:

```coq
v ←ω kernel partial tt ;;
ηω (FHRet v)
```

Read this as: sample the native round outcome `v`, then return the stable
head `FHRet v` as a value of the formal measure. These are three different
levels: program `Ret v`, stable head `FHRet v`, and measure return `ηω x`.
In AbsorbingFrontier, `b ←ω vn_fair ;; reveal_front b` instead selects a
frontier which may contain a visible head and its entire continuation.

`supω` is **syntax, not a certificate of a mathematical supremum**. The
constructor still accepts arbitrary sequences, including invalid ones.
Increasingness, modelability and semantic lub statements remain separate
proof obligations. In particular, notation does not identify a raw `FOLub`
with an independent domain's lub. The implementation/theory files retain
their constructor names. The tutorial and case-study clients use this notation
where it makes the program/frontier/measure distinction easier to read.

## Reading semantic measure algebra

Native `MN` and frontier `MF` share an opt-in interface notation. It lives
beside the operations, not in a backend or a new facade:

```coq
From PTree.Prob.Interface Require Import Measure Omega.
Import SemanticMeasureNotations SemanticOmegaNotations.
Local Open Scope semantic_measure_scope.
```

| Notation | Exact expansion |
|---|---|
| `ηₘ x` | `sem_ret x` |
| `mu >>=ₘ k` | `sem_bind mu k` |
| `mu ≈ₘ nu` | `sem_eq mu nu` |
| `mu ≈[RR]ₘ nu` | `sem_lift RR mu nu`, including heterogeneous return types |
| `⊥ₘ` | `sem_zero` |
| `mu ≤ₘ nu` | `sem_le mu nu` |
| `chain ⇑ₘ out` | `sem_lub chain out` |

After importing the notation modules, `(expression)%sm` also works without
opening the scope. `Measure` alone supplies the first four symbols;
`Omega` supplies the last three. Bind associates to the left and binds more
tightly than the relations, so the left-unit law reads:

```coq
ηₘ x >>=ₘ k ≈ₘ k x
```

The subscript marks **SemanticMeasure**, not specifically MN: the same
notation works for native and frontier carriers. It does not choose a
`SemanticMeasure` instance, register hints, or invoke canonical routing.
Where the interpretation is ambiguous, retain an explicit instance/profile;
shorter notation is not a reason to weaken that distinction. Raw FreeOmega
`ηω / ⊥ω / supω` describe raw syntax; program `Ret / bind / ≈ₚ` describes trees.
`≈ₘ` and `≈[eq]ₘ` remain distinct interface projections; the notation adds no
law identifying them.
In particular `chain ⇑ₘ out` asserts a **relation**, not a constructor or
an automatic proof that an arbitrary chain has a supremum.

MixedHead uses this algebra for finite kernels and the heterogeneous
3-to-2 lifting. IterationBasics uses it for frontier equality and native
limits; AbsorbingFrontier uses it for whole-head relational lifting. Explicit
backend configuration and probability-analysis proofs remain in place.

## Reading the external model

External validation examples may additionally opt into bounded-expectation
order, defined alongside `OmegaVal` in `Prob/Domain/Expectation.v`:

```coq
From PTree.Prob.Domain Require Import Expectation.
Import OmegaValNotations.
Local Open Scope omegaval_scope.
(* L ≤ᵥ M is oval_le L M; (L ≤ᵥ M)%ov also works. *)
```

This does not introduce a probability-interface instance or import FreeOmega.
`oval_eq`, `oval_lub Hi`, `oval_eval`, `oval_mass` and `oval_coupled` retain their
names. In particular, the lub still requires its increasingness certificate;
bidual constraints are not presented as actual coupling existence. Modelability,
denotation and qlift retain their explicit names. Stable hitting has the
separate tree-facing judgment syntax described below.

## Reading stable frontiers

The existing definition owners provide opt-in client judgments; no new
semantics, wrapper definition, backend selection or typeclass is introduced:

```coq
From PTree.Eq Require Import UnifiedFrontier PTreeKernel.
Import HittingNotations FrontierCertificateNotations.
Local Open Scope hitting_scope.
```

| Client notation | Exact expansion |
| --- | --- |
| `t ⇓ₕ front` | `ptree_stable_hitting (observe t) front` |
| `t ⇓ₕ¹ front` | `ptree_stable_hitting_ast (observe t) front` |
| `hit[n] t` | `ptree_hitting_approx n (observe t)` |
| `t ⊢F front` | `frontier_certificate (observe t) front` |

The delimiter is `%hit`. `HittingNotations` belongs to `PTreeKernel`;
`FrontierCertificateNotations` belongs to `UnifiedFrontier`. The latter
does not import the semantic kernel merely to declare certificate syntax.
The caller still chooses `MF`, `FI`, `MX` and `FO`, exactly as for the raw
judgments. In particular, these symbols do not select structural FreeOmega
equality instead of the observable profile.

`hit[n]` counts internal fuel: Ret and Vis are already stable at zero fuel;
Tau and Prob spend fuel. `⇓ₕ` specifies a complete distribution of stable
heads, permitting missing mass. `⇓ₕ¹` additionally asserts `sem_total`;
for a subprobability backend that is stable mass one, **not necessarily
termination at a return**: an offered Vis head is also stable. `⊢F` is a
syntax-directed certificate and is not interchangeable with either semantic
judgment. Its soundness uses the existing certificate soundness theorem and
its premises.

The same finite/complete distinction reads directly as:

```coq
(* With the same explicit semantic profile throughout: *)
hit[n] t ≤ₘ hit[S n] t
(fun n => hit[n] t) ⇑ₘ front
t ⇓ₕ front
```

The last two propositions are definitionally equal. The first is a theorem
under the existing order/omega laws, not something notation assumes.
`supω n, ...` remains raw FreeOmega syntax; this notation change does not
turn arbitrary sequences into increasing chains.

Actual case-study statements now read:

```coq
Lemma round_complete partial i : step partial i ⇓ₕ round_front partial i.
Theorem loop_frontier_exact partial : loop partial ⇓ₕ loop_front partial.
Theorem endless_frontier_zero : endless ⇓ₕ ⊥ω.

Lemma loop_hits s : raw_loop s ⇓ₕ loop_heads s.       (* Adaptive *)
Theorem raw_loop_ast s : raw_loop s ⇓ₕ¹ loop_heads s.

Theorem random_walk_ast : random_walk ⇓ₕ¹ random_walk_heads.
```

RandomWalk's `walk_hitting` and `joint_hitting` definitions use `hit[fuel]`;
FactoryController and AbsorbingFrontier use `⇓ₕ` for their mixed Ret/Vis
frontiers. The analysis, coinduction and algebraic proof chains are unchanged.

The frontier-composition helper is now `bind_frontier`, so bind results can
be read as `front >>=ₘ bind_frontier k fronts`. Its old name
`stable_head_bind_front` is removed, without a compatibility alias.

We deliberately do **not** mechanically strip every `ptree_` prefix:
`PrimitiveStableHitting.stable_hitting` is the arbitrary-kernel definition,
and `PEutt.stable_hitting_ret/prob` already name related laws at a different
layer. The explicit low-level names disambiguate these owners; the client
judgments remove that noise without adding competing short-name aliases.
`SHInternal`, fuel indices, theorem hypotheses and module paths are unchanged.

Technical checks live in the non-installed
`tests/Notation/HittingNotation.v`: exact expansions, scope separation,
finite/complete judgments, certificate distinction, measure-notation
precedence and observable-profile inference.

## Case-study presentation policy

Program code uses `sample`, `trigger` and `x <- t ;; k x` where these express
the intended atomic operation or sequencing. Native and frontier algebra use
the selected `ₘ` interface; raw frontier expressions use `ηω / ⊥ω / ←ω / >>=ω / supω`.
Do not insert a new program bind merely to conceal a constructor when a proof
needs that exact visible continuation or finite-step observation.

- **FactoryController:** sequential state/device actions and scripted handlers;
  the complete five-step sampler rewrite remains in the main proof. The
  next-device frontier and its query use the measure notation.
- **AdaptiveFactoryController:** sequential interleaving of samples and events;
  finite distribution algebra and fair frontiers stay visually separate.
- **MixedHead:** the explicit 3-to-2 joint and up-to proof remain visible;
  the two sampled frontiers now use the same syntax as the tutorials.
- **IterationBasics / AbsorbingFrontier:** atomic samples, program composition
  and formal limits; exact visible continuations are retained in head values.
- **RandomWalk:** passage sequencing, native finite-observation algebra and
  formal limits. Raw `Prob` remains where the proof counts exact sample/Tau
  steps; harmonic and infinite-support arguments are not disguised as rewrites.
- **InteractiveVonNeumann:** the formal frontier limit uses `supω`; explicit
  request/reply `Vis` guards remain in the coinductive service.

Neither backend choices nor probabilities, state updates, iteration schedules,
relation definitions or proof-method boundaries are changed by this policy.

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

For genuine order-theoretic leastness, see [ReturnIteration](ITERATION.md#return-only-frontiers-and-classical-iteration):
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
- MathComp retains its explicit mathematical conditions and isolated
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

## Factory controllers

[FactoryController](../theories/Examples/FactoryController.v) is the first
whole-program rewrite case. Read its actual controller programs, then
`Rewriting.factory_controller_program_rewrite`: sampler refinement, handler
and State equations compose inside the infinite device service. The private
sampling analysis is reused, not re-proved as part of the rewrite chain.
Its native backend is SubEnumQ throughout: VN draws, binary factory,
State/device handlers and executable roots. `BoundedVonNeumann.sampler_fair`
connects the bounded two-draw retry program to the existing scalar VN
convergence certificate, and `BoundedFactory.fair_factory_direct` supplies
the second component equation. EnumQ is only a finite-analysis projection;
there is no runtime conversion of an EnumQ tree. Native probability validity
is intrinsic, so the old case-local `Probability` module is unnecessary.
The quantitative endpoint uses the bounded query notation `Prₛ`.
The short `Facts` corollaries likewise import `FreeOmegaRewriting`: bind,
iteration, State and Exception congruences come from the library, with no
controller-specific Proper registrations. The pointwise step equation is
rewritten under iteration; the resulting service equation is rewritten under
the handler stack.
`Observation.mode_measure_probability` uses pointwise finite-expectation
extensionality rather than function equality; its proof is closed under the
global context.
`Observation.factory_next_action_probability` is a separate quantitative result;
scripted and live extraction execute the named programs rather than reimplementing
the algorithm. See [Execution](EXECUTION.md) for runtime trust limits.

[AdaptiveFactoryController](../theories/Examples/AdaptiveFactoryController.v)
adds persistent state changes between failed attempts. In namespace `Adaptive`,
start with the claim `controller_refinement`, then read its full calculation
in `controller_program_rewrite`, with `adaptive_factory_direct` and
`raw_loop_fair` as component endpoints. The selected backend is SubEnumQ;
raw EnumQ belongs only to finite analysis. Bit observations and relational
support suffice: there is no artificial requirement to solve for an explicit
finite joint limit of state and bit. State is not reset between retries, and
no independence assumption may replace the correlated-state proof.

The private state contains `health : bool`, selecting the next attempt's
source (`1/3` or `1/4`), and a single `retries : nat` counter. The counter is
updated only by `Retry` on a failed attempt; it never feeds into sampling or
control flow. `ChooseSource` binds `src` once; both draws in that
attempt use it even though `CheckSensor` and the health update occur between
them. Equal draws retry with the updated health, unequal draws return the
first bit with the actual private state. The recurrence remains state-dependent;
symmetry and the uniform `5/8` retry bound yield the fair-bit law.
`lower_attempt` exposes the shared source and `failed_branches_persist` checks
the two retry successors. `two_attempts_are_adaptive` computes unresolved mass
`55/162` after two attempts, different from the fixed-source value `(5/9)^2`.
The `repairs`/`rounds` counters and `Maintenance`/`Round` events have been
removed. `Retry` remains as the one bookkeeping effect; iteration itself
expresses retry control flow and factory rounds.
The sampler, factory and persistent `Request`/`Emit` refinement endpoint names
are unchanged. Sampler/factory refinement relates the returned bit without
constraining the private health or retry count; service/controller refinement
preserves the public interaction while hiding that state.

For MixedHead, read `masked_protocol_equivalent` in `MixedHead/Protocol.v`;
`MixedHead/UpTo.v` provides the independent staged appendix proof.
The implementation's multi-draw Boolean sampler and specification's one-shot
sample have different internal shapes. The proof builds the finite sampler
coupling where needed, then uses up-to-bind/Vis at loop entries. The same
nonfunctional 3-to-2 joint relates both heterogeneous return payloads and
recursive hidden states. `masked_public_protocol_equivalent` forgets private
payloads; the separate Reply query retains original mass without normalization.

Auxiliary lemmas should expose reusable analysis or real structure, not hide
the whole program transformation. The [standard](CASE_STUDY_STANDARD.md)
requires readable composition, not a fixed tactic sequence. Program sources
are the authoritative detailed proofs; this guide does not duplicate them.
