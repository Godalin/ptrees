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
| [MixedHeadProtocol](../theories/Examples/MixedHeadProtocol.v) | Complete programs (§2), then the in-place compositional proof `masked_protocol_equivalent` (§4), with no bridge premise | A branching Boolean sampler versus a one-shot specification, related through finite stable hitting and up-to-bind. The same non-functional 3-to-2 joint abstracts heterogeneous Ret payloads and recursive Vis continuations. `masked_public_protocol_equivalent` erases the payload; `masked_challenge_true_reply_probability` retains the `3/8` and `1/8` queries. No execution endpoint is claimed. |
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
| `x <~ mu ;; t` | `FOSample mu (fun x => t)`: native sampling |
| `ωsup n, t` | `FOLub (fun n => t)`: formal countable completion |
| `↑ω mu` | `free_omega_sample mu`, definitionally `FOSample mu FORet` |

The definition module opens no scope for clients; `(expression)%fo` also works without
opening the scope. Native sampling `<~` is deliberately distinct from program
sequencing `<-`. No typeclass selects a measure interpretation here, and no
equality/lifting relation is redefined. Semantic clients use `>>=ₘ` for bind
on their selected FreeOmega measure instance. Syntax-only proofs retain
`free_omega_bind`: notation must not add native capabilities or require an
observable instance just to manipulate the datatype.

For example, the complete silent-round frontier in IterationBasics reads:

```coq
v <~ kernel partial tt ;;
ηω (FHRet v)
```

Read this as: sample the native round outcome `v`, then return the stable
head `FHRet v` as a value of the formal measure. These are three different
levels: program `Ret v`, stable head `FHRet v`, and measure return `ηω x`.
In AbsorbingFrontier, `b <~ vn_fair ;; reveal_front b` instead selects a
frontier which may contain a visible head and its entire continuation.

`ωsup` is **syntax, not a certificate of a mathematical supremum**. The
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
`ηω / ⊥ω / ωsup` describe raw syntax; program `Ret / bind / ≈ₚ` describes trees.
`≈ₘ` and `≈[eq]ₘ` remain distinct interface projections; the notation adds no
law identifying them.
In particular `chain ⇑ₘ out` asserts a **relation**, not a constructor or
an automatic proof that an arbitrary chain has a supremum.

MixedHead uses this algebra for finite kernels and the heterogeneous
3-to-2 lifting. IterationBasics uses it for frontier equality and native
limits; AbsorbingFrontier uses it for whole-head relational lifting. Explicit
backend configuration and probability-analysis proofs remain in place.

For the initial notation-only migration from `e78a1bc`, 18 affected definitions and
theorems (including the MixedHead public results and the two tutorials'
frontier relations) were compared before/after using compiled types and
`Print Assumptions`: all were identical. The existing 491-entry main and
129-entry generic algebra contract groups are also unchanged. No snapshot, instance registration,
capability declaration or trust policy was modified. Scope separation,
heterogeneous lifting, bind precedence and high-universe carriers are checked
by the non-installed `tests/Notation/SemanticMeasureNotation.v` client.
Local validation passed: full root `dune build -j 2` (including AllImports
and extraction), 140 Python tests, and 39 execution/safety tests rerun after
re-extraction. Architecture, API, source-safety and contract-registry checks
passed. The two-file Gate M boundary is unchanged; full build is not a claim
that Gate M is universe-checked. No remote CI or new kernel audit was run.

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
`ωsup n, ...` remains raw FreeOmega syntax; this notation change does not
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

Validation against `f25991b`: 17 affected declarations retain their compiled
types and `Print Assumptions` (modulo the single helper rename and printer
whitespace). The changed non-example theory/check files preserve their exact
source apart from that rename and the appended notation blocks. The existing
491 main contracts, 129 generic-algebra contracts and 47 FactoryController
contracts pass; the main snapshot changes only the two literal occurrences
of the renamed helper, with no assumption or other signature refresh.
Full local `dune build -j 2` (including AllImports and extraction), 140 tool
tests, 39 post-extraction execution/safety tests, architecture, API-surface
and soundness-source checks passed. A joint `coqchk -norec` checked the two
definition owners, notation client and five migrated cases; dependencies were
not rechecked. The final notation client was checked again after adding its
negative probes. Gate M remains the same two files, outside the safe kernel
check; full build does not claim Gate M is universe-checked. No CI was queried.

## Case-study presentation policy

Program code uses `sample`, `trigger` and `x <- t ;; k x` where these express
the intended atomic operation or sequencing. Native and frontier algebra use
the selected `ₘ` interface; raw frontier expressions use `ηω / ⊥ω / <~ / ωsup`.
Do not insert a new program bind merely to conceal a constructor when a proof
needs that exact visible continuation or finite-step observation.

- **FactoryController:** sequential state/device actions and scripted handlers;
  the complete five-step sampler rewrite remains in the main proof. The
  next-device frontier and its query use the measure notation.
- **AdaptiveFactoryController:** sequential interleaving of samples and events;
  finite distribution algebra and fair frontiers stay visually separate.
- **MixedHeadProtocol:** the explicit 3-to-2 joint and up-to proof remain visible;
  the two sampled frontiers now use the same syntax as the tutorials.
- **IterationBasics / AbsorbingFrontier:** atomic samples, program composition
  and formal limits; exact visible continuations are retained in head values.
- **RandomWalk:** passage sequencing, native finite-observation algebra and
  formal limits. Raw `Prob` remains where the proof counts exact sample/Tau
  steps; harmonic and infinite-support arguments are not disguised as rewrites.
- **InteractiveVonNeumann:** the formal frontier limit uses `ωsup`; explicit
  request/reply `Vis` guards remain in the coinductive service.

Neither backend choices nor probabilities, state updates, iteration schedules,
relation definitions or proof-method boundaries are changed by this policy.

The continuation from `46cd2f4` renames raw return/zero to `ηω / ⊥ω`, removes
the redundant `>>=ω`, and adds opt-in `≤ᵥ` in the existing definition owners.
No new notation file, class, hint, semantic law or checker relaxation is added.
The seven primary examples listed above and two external-validation examples
are migrated; supporting mathematical developments are not mechanically
symbolized. Five controller/handler definitions were additionally compared
with their old bodies by `reflexivity`, confirming definitional equality.

Local validation: full root `dune build -j 2`, including AllImports and
extraction; 140 tool tests; 39 execution/safety tests rerun after extraction;
architecture, API and soundness-source checks. The 491 main, 129 generic-algebra,
47 FactoryController and 266 API owner/helper compiled type/assumption
contracts are unchanged, without refreshing their snapshots. Only the two
source-policy entries for the retired raw-bind notation tests are removed;
semantic bind precedence and observable-instance selection remain tested.
Gate M is unchanged and is not claimed to be universe-checked. No remote CI
or additional kernel audit was run.

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
