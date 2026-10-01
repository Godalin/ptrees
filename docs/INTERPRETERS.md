# Handlers, transformer folds and the ITree connection

PTree behavioral interpretation and execution into another monad are distinct
layers. Neither handler preservation nor a fold equation proves that an arbitrary
sampling implementation has the right probability law.

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
peutt RR (interp h1 t) (interp h2 u)
```

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
interp_itree h t = PTree.interp h (from_itree t)
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
