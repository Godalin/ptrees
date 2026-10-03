# Handlers, transformer folds and the ITree connection

The general interpretation is `fold(handle, sample)`: it interprets external
events and native sampling separately. `interp handle` is its specialization
to a target with a selected `MonadSample MN T` operation. This follows the
[`fold`/`interp` organization of CTree](https://github.com/vellvm/ctrees/blob/cabcf9bf24b0f459204a7da19ac01b7697ff04e3/theories/Interp/Fold.v).
Neither the sampling operation nor an interpreter equation certifies an
arbitrary implementation's probability law.

## General fold and selected sampling

[`Core/MonadSample`](../theories/Core/MonadSample.v) contains only
`msample : forall X, MN X -> T X`. It is an operation, not a probability
interface or a realization axiom. PTree selects its existing
`sample mu = Prob mu Ret`; `StateFold.MonadSample_stateT` reuses `state_sample`,
threading the unchanged state around the base sampling operation.

[`Core/Fold`](../theories/Core/Fold.v) provides:

```text
fold handle sample : ptree E MN A -> T A
interp handle     = fold handle msample
```

Definitions require Monad/MonadIter operations only. Laws need a lawful
target; a bare MonadIter does not imply even an unfolding or bind law.
Explicit `fold` remains useful when choosing between multiple samplers.
There is no default instance interpreting arbitrary native measures in ITree
or host IO: the client must choose that operation.

The public construction entry point `From PTree Require Import PTree` exports
`fold`, `interp`, `MonadSample` and its PTree instance. `PTreeFacts` additionally
exports the PTree-target laws and StateT interpretation. The former productive
`PTree.interp` is now named `PTree.interp_tree`; its implementation is unchanged.
[`Interp/FoldPTree`](../theories/Interp/FoldPTree.v) proves, for arbitrary
source trees and handlers:

```text
fold_ptree_interp : fold h PTree.sample t ≈ₚ PTree.interp_tree h t
interp_ptree_agrees : interp h t ≈ₚ PTree.interp_tree h t
```

The equality is behavioral, not definitional or lockstep structural:
fold delays after each sampling/handled operation, whereas productive interp
delays before entering a handler. A proof-only paced tree and finite scheduling
bounds (at most twice the depth) justify the same complete hitting limits.
Existing iteration congruence and unrestricted handler preservation then close
the agreement. No termination, visible-guard or total-mass condition is used.

`interp_ptree_ret/tau/vis/prob/bind/iter` and `interp_ptree_peutt` expose the
resulting computation, algebra and heterogeneous preservation laws. They reuse
the generic theory rather than copying FreeOmega proofs. The common profile
includes native Core, frontier Core/Bind/order/omega, cofinality,
diagonal/Fubini, bind/mixed-bind order, directed cofinality, selection and
relational mixed-bind/zero/lub. SubEnumQ and SubEnumR completion clients
discharge it. MathComp's existing Gate M client still explicitly assumes
coupling gluing and relational-lub closure; this work does not prove the latter
or enlarge the unchecked boundary.

`interp_state` is exactly the existing StateT fold with selected sampling.
`interp_state_run_state` specializes the existing uniformity square:

```text
interp_state handle t s ≃ interp handle (run_state t s)
```

It requires Eq1 equivalence, monad laws and iteration uniformity of the target,
not sampling correctness. ITree and PTree clients exercise the square. For the
PTree target, agreement then connects it to productive `PTree.interp_tree` after
`run_state`. Existing staged lowering in case studies is unchanged.

There is no probability `refine` API. Arbitrary-target laws and probability
preservation remain separate from selecting an operation; the existing ITree
fold laws also apply to `interp` by unfolding it. Migration is explicit:
`interpM` becomes `interp`, `interp_stateM` becomes `interp_state`, and
`interpM_ptree_*` becomes `interp_ptree_*`. No export-order alias chooses
between two meanings of `interp`.

The paper-facing distinction therefore matches the code:

```text
fold h g       explicit event and native-sampling algebras
interp h       target-selected sampling: fold h msample
interp_state h StateT instance, with sampling lifted through state
interp_tree h  productive PTree implementation, behaviorally agreeing with interp
```

[`PublicInterpretation`](../tests/Imports/PublicInterpretation.v) checks the
construction and reasoning entry points without implementation imports or
local sampling registrations. It checks the selected fold definition,
PTree agreement/bind and StateT sampling, and rejects the removed
`PTree.interp` name. The native and frontier probability obligations remain
explicit in the generic laws; this API migration does not strengthen them.

## Handler calculus

[`Core/Handler`](../theories/Core/Handler.v) defines
`Handler MN E F := forall X, E X -> ptree F MN X`, with `id_`, forward
composition `cat`, sum `case_`, injections, `bimap` and the empty handler.
These change the event signature, not the native sampling representation.
A handler need not be invertible, total, terminating or visibly guarded.

[`Interp/HandlerRelation`](../theories/Interp/HandlerRelation.v) defines
pointwise behavioral handler equality and proves replacement:

```text
forall X e, peutt eq (h1 X e) (h2 X e)
and peutt RR t u
------------------------------------------------
peutt RR (PTree.interp_tree h1 t) (PTree.interp_tree h2 u)
```

These existing calculus endpoints concern the productive implementation;
`interp_ptree_agrees` transports them to the public interpretation.
Both return carriers may differ. The fixed-handler `Unrestricted.peutt_interp`
is a specialization. Its machine separates source work from active handler
work; eliminated events become internal transitions. Finite scheduling and
complete-frontier fusion justify recursion instead of incorrectly treating
every eliminated source Vis as a target guard.

The unrestricted profile uses frontier Core/Bind/order/omega, cofinality,
bind/mixed-bind order, directed cofinality, diagonal/Fubini, selection and
relational zero/lub. Replacing handlers does not itself require a native
SemanticMeasure or relational mixed-bind. The weaker guarded route instead
uses an AE-visible condition on complete handler frontiers. Missing mass and
unbounded internal work are permitted by that condition.

`Interp/HandlerFacts` gives identity, trigger, composition congruence/units/
associativity, case injection/eta/composition, bimap congruence and empty-handler
uniqueness. These are modulo pointwise `peutt`, not Coq function equality.
Individual laws have different premises: identity and composition's right
unit use hitting/order continuity without relational-lub, whereas some trigger
and structural algebra laws use the structural bridge. Consult signatures
rather than imposing the strongest profile on every law.

`interp h` preserves Ret and bind behavior under the stated laws. It is a
monad-homomorphism-like interpretation, not an isomorphism. Completion-specific
endpoints in `Interp/FreeOmega/HandlerCompletion` only discharge probability
obligations; they do not duplicate the generic proof. Actual pointwise Proper
lemmas and opt-in completion registrations support contextual rewriting.

Interpretation does not preserve arbitrary transition bisimulation: handlers
can expose correlations that per-action transition comparison forgot. The
correlated two-round example demonstrates the distinction. MDP-fragment and
atomic-profile routes retain their separate conditions; see [MDP](MDP.md).

## Standard effects and stateful preservation

Use the established ITree event definitions where available; no parallel
PTree-specific State event family is needed. `Interp/State`, `Reader`, `Writer`
and `Exception` own program eliminators and their equation libraries.

`StatePreservation.run_state_peutt` proves:

```text
peutt RR t u
  -> peutt (fun (s,a) (s',b) => s = s' /\ RR a b)
           (run_state t initial) (run_state u initial)
```

The initial state is shared. Native probability, residual events, partial mass
and arbitrarily many updates remain allowed. This is not derived by pretending
mutable state is one fixed stateless handler: the machine threads `(state,tree)`.
Its profile uses frontier Core, the order/continuity/selection machinery and
relational bind/zero/lub, not full frontier BindLaws or native measure laws
directly. Existing structural State equations remain stronger endpoints.

Reader and Writer eliminate their effects while preserving residual effects
and sampling. Writer logs are ordered: commutativity is not assumed. Exception
elimination distinguishes a raised exception from probabilistic missing mass.
Effect algebra and Proper endpoints support rewriting under these eliminators;
do not infer arbitrary effect-order interchange or sample erasure from them.

## Transformer folds

`Core/Fold` separates `handle : E ~> T` from `sample : MN ~> T`.
MonadIter alone supplies an operation, not its laws. State/Exception fold
agreements need Eq1 equivalence, MonadLawsE and pure-map `iteration_uniform`.
The deliberately nonuniform option iterator remains a counterexample to
omitting this last premise.

| Effect | Concrete transformer | Proved fold agreement |
| --- | --- | --- |
| State | ITree state-first `stateT S T` | `fold_run_state`, generic lawful target |
| Exception | ExtLib `eitherT Err T` | `fold_run_exception`, generic lawful target |
| Reader | ExtLib `readerT Env T` | `itree_fold_run_reader`, actual ITree target |
| Writer | ITree log-first `writerT W T` | `itree_fold_run_writer`, actual ITree target + MonoidLaws |

Reader/Writer/Except transformer law constructors inherit uniformity from the
base. Writer uses explicit append operations and an accumulator iterator on
the log-first carrier; no commutative monoid is required. `Interp/FoldITree`
and `ReaderFoldFacts` / `WriterFoldFacts` prove actual computation and bind
equations. In particular Writer's bind combines output logs by append, not
merely by threading an opaque state.

State/Exception squares can now use PTree itself as the target via the full
[direct uniformity theorem](ITERATION.md). Reader/Writer's existing eliminators
insert administrative Taus, handled by ITree weak coinduction in their squares.
Arbitrary-target Reader/Writer commuting, all Conway/Elgot inheritance laws,
and blanket `peutt -> arbitrary fold equality` are **not** established.

## ITree embedding and sampling elaboration

[`Core/ITreeBridge`](../theories/Core/ITreeBridge.v) provides:

```text
from_itree       : itree E A -> ptree E MN A
interp_itree h t = PTree.interp_tree h (from_itree t)
elaborate       : itree (probE MN +' E) A -> ptree E MN A
elaborate_closed: itree (probE MN) A -> ptree void1 MN A
```

`from_itree` embeds Ret/Tau/Vis without Prob. Elaboration handles `Sample mu`
by native `sample mu = Prob mu Ret`, forwarding ordinary events with trigger.
Ret/Tau/Vis/bind/iter compatibility and the actual two-coins example connect
ITree's external sampling events to PTree's native probabilistic reasoning.
No execution entropy or normalization is involved.

Generic `Interp/ITreeEutt` and `ITreeReflection` prove:

```text
eutt RR t u <-> peutt RR (from_itree t) (from_itree u)
```

Preservation separates finite Tau-to-head exposure from pure silent divergence.
Reflection uses the probability profile's support/Dirac separation so that a
Dirac stable head cannot disappear into zero. The iff requires the combined
profiles, including relational zero for preservation; it is not asserted for
an arbitrary degenerate probability interpretation. FreeOmega supplies the
certificates for SubEnumQ/SubEnumR. Reflection's classical/dependent-equality
dependencies are recorded in the `itree_preservation` contracts.

The claim is precisely conservativity **on the image of `from_itree`**.
There is no `to_itree` reconstruction of every syntactically Prob-free PTree.
`interp_itree_eutt` and `elaborate_eutt` preserve equivalence, but have no
general reflection theorem: a handler can identify distinct source events.

Source interpretation compatibility is also proved: `from_itree_interp`,
`interp_itree_source_interp` and `elaborate_source_interp` relate handling
before embedding to handling afterward. Keep this square distinct from the
opposite-direction execution fold into ITree.

A source handler may transform Sample events, whereas an ordinary PTree handler
cannot transform native Prob. The general square lowers the entire source
handler; a stronger claim about handling only ordinary events after lowering
would need sample preservation.

## Reading and checking

Use `PTree PTreeFacts` plus an explicit backend for behavioral clients;
transformer/fold owners are opt-in. Read [FactoryController, Adaptive and
StateRewrite](CASE_STUDIES.md) for whole-program calculations.
[Verification](AUDITING.md) covers handler, effect, State/transformer and
ITree contract groups. Their existence does not discharge MathComp's explicit
gluing/relational-limit premises or expand its two-file Gate M exception.

`tests/Capabilities/MonadicInterpretation.v` checks completion clients for Q/R,
StateT inference and commuting, high-universe returns and nonreturning
source/handlers. The existing MathComp test file checks the conditional direct
instance. New types/assumptions are appended to the existing `effect_execution`
contract group; old entries are not regenerated. The generic agreement and
its derived PTree laws depend only on the already tracked `Eq_rect_eq`
logical axiom, besides their explicit semantic profile.
