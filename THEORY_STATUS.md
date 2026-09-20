# Maintained theory: current state

This document describes the maintained semantic objects, proved endpoints,
backend requirements and explicit boundaries. It is not a development log.
All paths below are relative to `theories/`. Historical implementations and
acceptance records remain in Git. The artifact targets Coq 8.20
(`>= 8.20, < 9.0`); the CI configuration pins 8.20.1. Local verification
does not imply a successful remote CI run.

## 1. Public semantic architecture

```text
PTree syntax
  -> primitive internal kernel
  -> complete stable hitting H(t)
       -> peutt / ≈ₚ                         whole-continuation coupling
       -> finite interaction observations    quantitative cylinders
       -> raw-tree observations/transitions
            -> tree_trans_bisim              response-wise coupling

peutt ⊆ tree_trans_bisim                      generic capability-qualified
peutt ⊊ tree_trans_bisim                      SubEnum/FreeOmega counterexample
peutt = tree_trans_bisim on mdp_state         fragment coincidence

labelled traditional MDP --encode--> mdp_state PTrees
```

`peutt` remains the canonical program equivalence; the independent
`tree_trans_bisim` is a comparison semantics, not its replacement.
`head_bisim` compares already-selected stable heads. These have different
domains or observation power and must not be interchanged by definition.
The generic facade `Eq/ProbabilisticSemantics.v` exposes curated vocabulary
and endpoint laws without re-exporting all proof machinery.
Comparison theory is imported explicitly from `Semantics/`.

### Representation, probability and stable hitting

`Core/PTreeDefinition.v` gives coinductive trees with Ret, Tau, Vis and
native Prob nodes, together with guarded bind, iteration and interpretation.
`SemanticMeasure` supplies measure operations and relational lifting; it
does not itself assert that every measure has mass at most one.
The node carrier `MN` represents sampling; the behavioral carrier `MF`
represents limits of internal computation. A `MixedMeasure MN MF` integrates
behavior against a native sample. This separation lets finite native
distributions generate unbounded behavior without pretending that their
finite representation is closed under countable limits.

`Eq/PrimitiveStableHitting.v` is syntax-independent. For an absorbing
kernel `K : S -> MF (stable_target S A)`, its finite approximants record the stable
outcomes reached within increasing internal fuel. `stable_hitting K s out`
is a **predicate** certifying a complete omega-limit witness `out`, not an
executable function selecting one measure. `stable_hitting_ast` adds
`sem_total out`. Finite and unbounded AST computations use the same
approximant/limit semantics; missing mass records internal divergence.

`Eq/PTreeKernel.v` instantiates this construction with PTree residuals and
stable heads `FHRet r` or `FHVis e k`. A visible head retains its **entire**
continuation. The kernel absorbs Tau and Prob, but does not consume an
external response until an observation/transition asks for one.

Existence follows from the order/omega capabilities; uniqueness follows
from the limit laws at the backend's equality-coupling level.
Generic theory must distinguish `sem_eq` from `sem_lift eq`; it does not
assume the latter reflects into the former.
`Eq/StableHittingRelation.v` supplies kernel-generic bidirectional matching,
monotonicity, and conversion between matching and chosen hitting witnesses.
Both behavioral relations reuse this infrastructure without defining one
relation in terms of the other.

### Canonical equivalence and stronger proof relations

`Eq/PEutt.v` defines `peutt RR` as a greatest fixed point: complete hitting
measures on both sides match through
`sem_lift (stable_head_rel RR sim)`.
The head relation matches returns by `RR`, and visible heads by the same
dependent event with related continuations for **every** response.
The generator contains no Tau, Prob, Bind, Iter, AST or certificate case.

The public notation is `t ≈ₚ u` and `t ≈ₚ[RR] u`, in `type_scope`.
The proof hierarchy is `pstruct ⊆ pstrong ⊆ peutt`:
exact structural lockstep, coupled-sampling lockstep, then extensional
behavior. The FreeOmega endpoints prove the inclusions.
There is no independent `pfinite` relation.

`Eq/StableHittingComputation.v` provides Ret/Vis characterizations, Tau
transparency, Prob decomposition/computation, Dirac and flattening laws,
and `peutt_iff_hitting`. `Eq/FreeOmega/Hitting.v` strengthens output
transport and Prob/Dirac/flatten calculation to backend-qualified iff laws.
Finite internal rewriting therefore calculates behavior and uses the
existing program congruences; it does not introduce another equivalence.

### Raw-tree transitions and the MDP fragment

The nine `Semantics/` modules keep definition and comparison layers separate:

| Module | Responsibility |
| --- | --- |
| `HeadTransition` | selected-head actions and independent head GFP |
| `MDPFragment` | unary coinductive invariant and raw-tree state predicate |
| `TreeTransition` | weighted raw-tree observations and action subkernel |
| `TreeTransitionBisim` | independent response-wise raw-tree GFP |
| `TreeTransitionSoundness` | direct canonical-to-transition inclusion |
| `MDPCoincidence` | generic fragment reverse implication and iff |
| `MDPCoincidenceFreeOmega` | proved FreeOmega separation endpoint |
| `MDPEmbedding` | labelled total MDP encoding and generic soundness |
| `MDPEmbeddingSubEnum` | concrete native reflection and encoding iff |

`head_step (FHVis e k) (Obs e x) out` means that `k x` completely
stable-hits `out`; Ret has no head step. No totality is required here.
`head_bisim` is a separate head-level GFP with per-action coupling;
its chosen-witness characterization and Equivalence instance are proved.

`mdp_head` is a unary greatest fixed point. Ret is admitted as a terminal
state. Every response at a Vis head must have a complete successor measure
that is total and almost everywhere supported on the same invariant.
`mdp_state t` requires an actual hitting witness `out`, a head `h`,
`sem_eq out (sem_ret h)`, and `mdp_head h`.
It does not demand a syntactically visible root. Conversely, an action
continuation may denote a non-Dirac distribution of MDP heads without being
an `mdp_state` itself. This is an MDP fragment **with terminal states**.

Raw-tree observations integrate projections over the entire current hitting
measure: Ret contributes its return value; Vis contributes its dependent
offered event. For a label `(e,x)`, `head_action_result` assigns a matching
head its real successor hitting measure, and an unmatched head zero.
`tree_trans` binds these contributions against the original frontier.

Thus transitions are unnormalized, mass-weighted aggregates, not selection
of a supported head and not conditional normalization. They are zero-totalized:
even Ret has a zero transition witness. Existence of a transition is not
enabledness. Separate return and offered-event observations are essential,
including for events with empty response types.

`tree_trans_bisimF RR sim` matches all three:
returns under `RR`, offered events under equality, and every label's
successors under
`fun h k => sim (stable_head_tree h) (stable_head_tree k)`.
It does **not** use `stable_head_rel sim` for those successor pairs, nor
mention `peutt` or `head_bisim` in its definition. Fold/unfold, coinduction,
reflexivity and arbitrary-witness endpoints are available.

On SubEnum/FreeOmega the inclusion is strict: fair mixtures of continuation
rows `(false,false)/(true,true)` and `(false,true)/(true,false)` agree
response-wise but admit no whole-continuation coupling.
This separates `forall response, exists coupling` from
`exists whole-head coupling, forall response`.

On `mdp_state`, the current hitting measure is Dirac up to semantic
equality, so that distinction disappears. The reverse proof retains actual
hitting witnesses and transports their couplings; it does not assume
hitting is closed under arbitrary output equality. After a response, an
auxiliary distribution invariant handles non-Dirac successors, and
`mdp_head` supplies recursive AE closure. Totality remains part of the
fragment definition but is not used by this reverse argument.
No larger fragment or arbitrary-fragment representation theorem is claimed.

### Finite interaction observations

`Eq/ProbabilisticTrace.v` defines an event selector
`forall X, E X -> option X`: it both recognizes an event and supplies the
environment response. A list of selectors is a `finite_interaction_pattern`,
possibly accepting more than a single concrete trace.
Queries recurse through stable hitting with AE continuation obligations.

Existence, uniqueness up to equality coupling and preservation by `peutt`
are proved. `finite_interaction_sem` chooses a representative by classical
choice; the function itself is not a canonical executable probability
measure. The meaning is well-defined up to the exposed semantic coupling.

`ProbabilisticTraceSubEnum.v` provides the bounded numeric predicate
`Prₛ[t | pattern] = p`, relating a valid query to an observable representative
and an indicator expectation; every such value lies in [0,1].
The raw Enum wrapper `Prₜ` remains a weighted compatibility endpoint:
without a separate program probability contract its numbers are weights,
not intrinsically bounded probabilities. Neither wrapper computes by
inspecting the arbitrary choice-selected representative.

## 2. Capability and backend matrix

Structures use noun names: `SemanticMeasure`, `SemanticOmega`,
`MixedMeasure`. Property packages retain `Laws`. The legacy
`MeasureInterface` is distinct and is not the new semantic interface.
The maintained probability pairs are
`SubEnum -> FreeOmega SubEnum` and
`MathCompKernelMeasure -> FreeOmega MathCompKernelMeasure`.

| Capability | SubEnum node | raw Enum node | MathComp node | FreeOmega behavior |
| --- | --- | --- | --- | --- |
| Every native measure has mass ≤ 1 | intrinsic | no | intrinsic | inherits valid-node behavior |
| Measure structure / AE lift | yes | yes | yes | yes |
| Core, including coupling composition | yes | yes | explicit gluing | from node core |
| AE Kleisli / exact Dirac AE / countable AE | yes | yes | yes, without gluing | derived capabilities |
| Coupling AE transport/restriction | yes | yes | yes, without gluing | derived |
| Exact bind-AE support | yes | yes | yes, without gluing | used in mixed node-bind |
| Relational kernel-bind coupling | yes | yes | intentionally not supplied | proved directly |
| Order / omega / cofinality | node-specific | node-specific | node-specific | maintained profile |
| Omega AE / diagonal / Fubini | not the node obligation | not the node obligation | not the node obligation | derived |
| Mixed unit / node-bind / omega | pair-level | pair-level | pair-level | maintained profile |
| Mixed commutativity | optional | optional | optional | not a required capability |

`Regression/Backend/BackendCapabilities.v` checks the profiles.
Foundational MathComp AE laws are checked without
`MathCompCouplingGluing`; only its relational core needs that hypothesis.
The missing MathComp node bind capability is coupling through a kernel,
not ordinary measure bind. Its behavioral FreeOmega layer already has
relational bind; matrix symmetry does not justify an additional joint-kernel
selection development.

`SemanticSubprobability` exposes validity of an individual measure.
`SemanticSubprobabilityLaws` provides equality/return/bind closure.
`SemanticSubprobabilityCarrierLaws` certifies all carrier inhabitants.
Raw Enum has the predicate and closure laws but deliberately not the last
package. `Core/PTreeProbability.v` proves program well-formedness closure
under bind, fmap, guarded iter and the supported interpretation contracts.
These contracts do not assert AST; termination and normalization are
different obligations.

FreeOmega is a formal completion with an observable quotient, not an
unconditional concrete measure for every raw expression. Cofinality,
source/kernel diagonalization and sample-limit exchange require increasing
chains. Observation of a Lub also requires increasing **raw** approximants,
not merely convergence of their observable images. The disappearing-atom,
moving-diagonal and escaping-mass regressions enforce these boundaries.
No unrestricted interchange of two arbitrary convergent sequences is valid.

`FreeOmegaNativeCouplingLaws` is an optional measure capability, not a
program relation. SubEnum realization is proved by finite presentations,
bounded-test/Hall inequalities, rational transport and exact marginal
reconstruction, allowing heterogeneous carriers, noninjective decoders and
empty carriers. Raw Enum has an analogous native transport result.
MathComp's `mathcomp_coupling_realization` repackages an existing native
joint without gluing; this does **not** supply quotient-to-native
`FreeOmegaNativeCouplingLaws` for MathComp.

## 3. Theorem inventory and assumptions

The tables summarize capabilities, not every implicit parameter. Source
statements are authoritative. Capability hypotheses are distinguished from
global logical dependencies: a theorem closed under the global context can
still quantify over measure-law records.

### Hitting, algebra and guarded reasoning

| Endpoint / family | Content and boundary |
| --- | --- |
| `stable_hitting_exists`, `stable_hitting_unique` | complete limit existence and equality-coupling uniqueness under order/omega laws |
| `stable_hitting_ret_iff`, `stable_hitting_vis_iff`, `stable_hitting_tau` | stable constructors and weak internal Tau |
| `stable_hitting_prob_compute`, `stable_hitting_prob_decompose` | AE integration of branch behavior; decomposition uses witness choice |
| `peutt_of_hitting_lift`, `peutt_hitting_lift`, `peutt_iff_hitting` | complete-head coupling introduction/elimination |
| `peutt_equivalence`, Ret/Vis/Tau/Prob laws | canonical equivalence and derived constructor equations |
| `peutt_coinduction`, `peutt_coinduction_upto` | postfixed-point and already-proved-equivalence closure |
| `peutt_coinduction_upto_bind` | proved heterogeneous bind-compatible closure, not an axiom |
| `peutt_preserves_hitting_mass`, `peutt_not_of_mass_mismatch` | preserved mass and divergence-sensitive separation |
| `FreeOmega.Bind.peutt_bind` | arbitrary eventful bind congruence; generic diagonal scheduling discharged by `ptree_bind_approx_cofinal_all` |
| `FreeOmega.Algebra` | Monad/Functor laws; Proper instances for constructor, measure, bind, fmap and renaming rewriting |
| `pstruct_iter_split_at` | generic stopping/barrier decomposition, no probability or eventual-hitting premise |
| `pstruct_iter_natural`, `pstruct_iter_codiagonal` | structural iteration identities with canonical peutt endpoints |
| `peutt_iter_rel` | heterogeneous fusion under structural step relations |
| `peutt_iter_behavioral_rel` | behavioral step fusion for eventless unbounded loops |

`Eq/FreeOmega.v` aggregates the backend equational theory. All maintained
probabilistic GFPs use coq-coinduction; Paco is an inherited ITree dependency.

Interpreter laws include structural preservation, bind/iter morphisms,
effectful-handler composition, structurally related handler replacement,
and full behavioral preservation for pure event renaming. Identity and
composition of translation are behavioral, accounting for administrative Tau.
`ptree_interp_approx_cofinal_all` and `ptree_stable_hitting_interp`
establish the general scheduling/complete-limit composition theorem.

Full preservation by an arbitrary effectful handler is still conditional:
`Eq/FreeOmega/Interp.v` isolates `interp_vis_fusion`, and
`peutt_interp_of_vis_fusion` derives preservation from it.
The unresolved part is progress when an internally returning handled Vis
continues into the next interpreted continuation before exposing a stable
head. Ordinary up-to-bind compatibility is proved but does not justify an
unguarded use of the desired interpreter theorem.
Eventful behavioral iter fusion has the analogous candidate-closure boundary.

The first [interpretation-compositionality stage](docs/INTERP_COMPOSITIONALITY.md)
now proves that `tree_trans_bisim` is **not** an arbitrary-interpreter
congruence. `Regression/Semantics/InterpExposure.v` reuses the 2x2 source pair
and replaces one Query by two, ignoring the first answer. The first target
action exposes a distribution of second-round states for which no single
coupling can match both possible second answers. Current return and event
observations still agree. The handler already has a Dirac visible first
head, so visible guarding alone cannot suffice for transition preservation.
This does not settle peutt preservation: the source pair is not peutt-related.
Stage 2 now supplies `Eq/FreeOmega/GuardedInterp.v`: `guarded_handler`
requires every complete handler hitting witness to be AE-supported on Vis
heads, without totality or a syntactic-prefix restriction.
`guarded_handler_vis_fusion` proves the existing fusion obligation by
AE-restricting the handler's diagonal coupling and using up-to-bind at the
first visible guard. `peutt_interp_guarded` then derives heterogeneous
return-relation preservation from the existing theorem. An explicit
`peutt_interp_guarded_Proper` endpoint supports local setoid rewriting.
The same stage-1 handler preserves peutt despite its transition counterexample;
additional regressions check partial divergence and null return branches.
Stage 3 supplies `Semantics/AtomicInterp.v`: an explicit `atomic_handler`
certificate for response-preserving event permutations. Its two semantic
clauses require complete Dirac hitting at one renamed Vis head, and at
`Ret x` after response `x`, without a finite-fuel or syntactic restriction.
`tree_trans_bisim_interp_atomic` is proved by a direct transition-GFP
postfixed argument, for arbitrary `RR` on a common return carrier.
The proof transports return/event projections and mass-weighted action
successors; it does not assume peutt of the source trees. This is a sufficient
profile, not a characterization: event merging, response transformations,
and multi-interaction handlers are not covered. Regressions preserve the
non-peutt 2x2 pair, check a non-identity event permutation (including empty
response events), and rule out atomicity for the two-query counterexample.
Stage 3 was accepted at `8e09561`. Stage 4 adds `Semantics/MDPInterp.v`:
`mdp_handler` is a local contract preserving selected MDP heads under the
existing `ptree_interp_head_tree`. `mdp_state_interp` extends it to arbitrary
raw MDP states. The generic contract and guarded compositionality route
support distinct effect signatures `E -> F`; coincidence is stated on the
target signature `F`. The accepted atomic permutation profile and SubEnum
atomic endpoints remain `E -> E`. Atomic handlers discharge the contract by unary
coinduction, under an explicit total-head-map premise; abstract
`SemanticTotalProperLaws` alone does not supply that premise.
`Prob/FreeOmegaTotalSubEnum.v` proves totality under **every** value map on
SubEnum/FreeOmega by reducing total observations to unit observations.
Consequently `MDPInterpSubEnum.v` supplies atomic MDP preservation without
an extra client premise, including non-Dirac successor distributions and
unbounded interaction. Existing fragment coincidence is reused at the
interpreted states, and a direct transition-preservation proof can then be
converted to peutt. This is preservation, not source/target reflection;
there is no unconditional MathComp total-map specialization in this stage.
The proof approach of `c74ee64` was accepted; the `E -> F` follow-up awaits
final Stage 4 baseline acceptance. A genuinely heterogeneous regression
proves the handler contract independently and transports an infinite
Ask/Reply protocol across two distinct inductive event families. State
interpretation and directory moves have not started.

### Semantic comparison and classical MDPs

| Endpoint | Scope / important premises |
| --- | --- |
| `head_bisim` fold/unfold, coinduction, Equivalence | selected-head per-action coupling, not raw-tree bisimulation |
| `mdp_head_coinduction`, `mdp_head_successor_closed` | unary invariant; closure for any complete successor witness |
| `tree_trans_unique` and observation uniqueness | equality coupling, not assumed semantic-equality reflection |
| `tree_trans_bisim_coinduction` | independent three-observation GFP |
| `peutt_preserves_tree_trans` | arbitrary transition witnesses; relational bind and AE-restricted whole-head coupling |
| `peutt_tree_trans_postfixed`, `peutt_tree_trans_bisim` | direct general inclusion; common return carrier with arbitrary `RR` |
| `peutt_strictly_contained_in_tree_trans_bisim` | concrete SubEnum/FreeOmega proper inclusion, not every abstract lifting |
| `mdp_state_tree_trans_bisim_peutt` | generic reverse; existing behavior-level `SemanticMeasureDiracAELaws` |
| `mdp_state_peutt_tree_trans_iff` | unchanged MDP fragment on both sides; combines reverse and inclusion |
| `free_mdp_state_peutt_tree_trans_iff` | FreeOmega supplies exact Dirac AE structurally, no new global instance |
| `subenum_encode_mdp_state` | labelled total MDP encodes into the fragment |
| `subenum_mdp_head_bisim_iff`, `subenum_mdp_peutt_iff` | full correspondence on encoded MDPs, using proved native coupling reflection |

The FreeOmega coincidence endpoints use native Core, AELift, CouplingAE,
CountableAE and Omega capabilities, not a native relational bind law.
The MathComp instantiation retains explicit `MathCompCouplingGluing`.
The reverse generic proof needs neither order/existence laws nor classical
witness choice; the full iff inherits them from general inclusion.

The final composed statement
`mdp_bisim s t <-> tree_trans_bisim eq (encode s) (encode t)`
has **not** yet been packaged as a theorem. It is the reserved next theory
step, not a claim of this cleanup milestone.

`strictness_pair_outside_joint_fragment` proves that the strictness pair
cannot **both** satisfy the fragment premises, not that each was separately
shown outside it. `HeadTransition`, `MDPFragment`, `TreeTransition` and
`TreeTransitionBisim` remain independent of PEutt; negative import checks
guard this boundary.

### Quantitative endpoints and four case-study groups

| Group / endpoint | What is proved |
| --- | --- |
| `CaseStudies/MixedHeadProtocol.v`: `masked_protocol_equivalent` | flagship SubEnum mixed Ret/Vis whole-head coupling; response-dependent infinite continuations |
| same: `masked_challenge_true_reply_probability` | challenge/reply pattern probability 3/8 or 1/8 depending on the environment challenge |
| `CaseStudies/RandomWalk.v`: `run_split`, `passage_unfold`, `random_walk_bind` | structural barrier decomposition, behavioral renewal equation, normalization under arbitrary continuations |
| same: `random_walk_closed_form` | native AST and joint law Pr[(0,n)] = 2/3^n for n ≥ 1, zero elsewhere |
| `CaseStudies/InteractiveVonNeumann/`: `interactive_von_neumann_service_equivalent` | unbounded internal retries between infinitely many request/reply interactions |
| same: `von_neumann_request_true_reply_trace_probability` | concrete two-event cylinder has probability 1/2 |
| `CaseStudies/BernoulliFactory/`: `peutt_factory_vn_direct` | parametric compositional biased-coin-to-rational-coin equivalence |
| same: `probabilistic_factory_with_sampler` | probability contract preserved by the Factory context independently of termination |
| `finite_interaction_query_exists`, `finite_interaction_query_unique_up_to_coupling` | well-defined finite cylinder queries under the stated limit/bind/AE capabilities |
| `peutt_preserves_finite_interaction_sem` | behavioral invariance of the choice-packaged measure-valued semantics |
| `subenum_finite_interaction_probability_range` | every supplied bounded numeric probability witness lies in [0,1] |

Factory groups definitions, analytic certificates, ordinary Von Neumann
support, rational/real samplers, correctness and composition. The interactive
service reuses that support, not a copied extractor proof. Existing
`Operational*` basenames remain; this is classification, not theorem/API
renaming. The current VN service and rational Factory use raw Enum with
appropriate normalization/support proofs; MixedHeadProtocol and RandomWalk
use intrinsic SubEnum.

The compositional rational Factory endpoint proves the necessary support
facts; it does not need the older monolithic route's
`OperationalFactoryStepSupportLaws`. The MathComp real-oracle endpoint
still takes `MathCompOracleSupportLaws` as an explicit example-specific
support adequacy premise in addition to gluing. This must not be hidden
behind the general backend capability matrix.


RandomWalk's countable joint law is a limit of finite primitive observations,
not a countably supported SubEnum node or a proved geometric-sampler peutt
equivalence. Its rational harmonic bound constructs convergence and AST.

### Logical assumptions and mechanization boundaries

No additional measure axiom is introduced by the transition comparison or
coincidence. Existing capability parameters remain explicit. Representative
global dependencies are:

| Result | Global logical dependencies beyond capability parameters |
| --- | --- |
| generic hitting Ret/iff API, basic GFP coinduction | closed for the audited endpoints |
| `pstruct_iter_split_at`, RandomWalk `run_split` and harmonic bound | closed |
| fixed-witness `peutt_preserves_tree_trans` | inherited `eq_rect_eq` |
| general inclusion / full coincidence iff | additionally classical witness-choice principles from transition existence |
| 2×2 positive and negative witnesses | functional extensionality and `eq_rect_eq`; no classical witness choice |
| two-round interpretation exposure counterexample | functional extensionality and `eq_rect_eq`; no classical witness choice |
| guarded-handler fusion / peutt preservation / Proper | functional extensionality, `eq_rect_eq`, relational choice and dependent unique choice from existing hitting witness selection |
| atomic-handler transition preservation | functional extensionality, `eq_rect_eq`, relational choice, dependent unique choice, and excluded middle from existing transition witness existence |
| MDP handler head-to-tree preservation | `eq_rect_eq`, relational choice and dependent unique choice |
| atomic SubEnum MDP preservation / total-map theorem | functional extensionality, `eq_rect_eq`, relational choice and dependent unique choice; coincidence routes also inherit excluded middle |
| generic reverse coincidence | `eq_rect_eq` only |
| FreeOmega exact Dirac AE proof | closed; passed explicitly rather than a global instance |
| FreeOmega reverse coincidence | functional extensionality and `eq_rect_eq` |
| MathComp coincidence iff | existing extensionality/description principles, plus forward witness choice; gluing remains a parameter |
| RandomWalk closed-form result | functional extensionality and dependent equality |
| concrete SubEnum native realization | inherited classical/extensionality principles and standard-real construction dependencies |

The standard-real realization route uses the existing
`ClassicalDedekindReals.sig_not_dec` and `sig_forall_dec` dependencies;
finite rational matching/transport existence itself audits as closed.
A generic positive coupling interface need not separate observations.
Neither Dirac inversion nor arbitrary coupling-to-semantic-equality reflection
may be silently inferred from that interface.

`frontier_certificate`, finite-internal execution plans, kernel completion,
joint rounds and costed schedules are proof infrastructure, not additional
behavioral equivalences. They currently remain under `Eq/` pending a separate
namespace migration. [The complete layout/client audit](docs/LAYOUT_AUDIT.md)
records their actual imports, direct/transitive clients and zero-client
modules. No zero-client module is automatically treated as dead code:
public endpoints and independent regression leaves naturally have none.
The [move manifest](docs/module-moves.tsv) lists every namespace change.

`Regression/Infrastructure/AllImports.v` checks that all maintained modules
coexist in one universe context; CI checks its inventory is complete.
The older frontier/partial-divergence Enum regressions now use FreeOmega Enum
for behavior, avoiding incompatible constraints from using the same native
Enum universe for recursive heads. The [universe audit](docs/UNIVERSE_CONSISTENCY.md)
records the repair and its inherited scalar-model assumptions.

## 4. Non-claims and bounded next work

The maintained artifact does **not** claim:

- a probability measure on infinite traces, conditioning/MDP schedulers,
  general WP calculus, temporal logic or probabilistic metrics;
- full arbitrary-effectful-handler peutt preservation without
  `interp_vis_fusion`, or unrestricted eventful behavioral iteration fusion;
- exact no-Prob `peutt <-> ITree.eutt` from the generic positive interface;
- quotient-to-native coupling reflection for every backend;
- an additive interpretation of arbitrary non-increasing FreeOmega Lub terms;
- that raw Enum enforces native probability, or that AST follows from
  a well-formedness contract;
- strictness of transition inclusion for every abstract backend;
- reconstruction of every `mdp_state` as an encoded textbook MDP;
- the final MDP-encoding-to-tree-transition corollary before it is proved.

For no-Prob conservativity, concrete FreeOmega support and mass separation
already rule out the generic universal-lifting countermodel, but a maintained
ITree embedding, pure-tree zero/Dirac hitting classification (including spin),
and dependent visible-head inversion into eutt remain unproved.

Core semantic definitions remain unchanged by the layout cleanup and the
subsequent universe repair of two legacy regression backends. Internal
namespace migration, the final encoding corollary and a README theory-overview
rewrite remain separate reviewed milestones; no further case study is added.
