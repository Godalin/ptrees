# Arbitrary handler preservation

Current follow-up: [handler calculus](HANDLER_CALCULUS.md) generalizes the
machine relation to two pointwise behaviorally related handlers. The public
fixed-handler theorem retains its compiled type and assumptions, but now
specializes that generic proof. The counts and exact-source claims below
describe this report's original checkpoint; the new audit reconstructs that
snapshot before running its historical conservation checks.

Baseline: `525a57fc6e79e0e73e7a70ae98e77946af6371c4`.
The subsequent [State-indexed follow-up](STATE_PRESERVATION.md) closes the
State preservation item recorded as open at this checkpoint.
This is the eliminating/mixed-handler foundation for the effects/execution
roadmap. It does not change existing relations, canonical routing, probability
classes, the guarded theorem, State implementation, or MathComp trust boundary.

## Result and assumptions

`Interp/Unrestricted.peutt_interp` proves, for arbitrary `E`, `F`, native
`MN`, frontier `MF`, heterogeneous return relation `RR : A -> B -> Prop`, and
**any** handler `forall X, E X -> ptree F MN X`:

```
peutt_E RR t u
    -> peutt_F RR (interp handler t) (interp handler u).
```

There is no visible-guarding, totality, termination, bounded-internal-work,
or target-preservation premise. Direct returns, unbounded internal work,
probabilistic mixtures, and divergence are allowed. The statement is about
whole-continuation `peutt`, **not** response-wise `tree_trans_bisim`.
The earlier two-query counterexample for the latter is unaffected.

The theorem consumes existing probability capabilities:

* frontier Core/Bind laws and MixedMeasure operations;
* order, omega, constant/prefix cofinality and directed cofinality;
* bind-order and mixed-bind-order laws;
* diagonal bind continuity and double-limit Fubini;
* increasing-chain omega selection;
* the existing ordinary propositions `relational_zero` and `relational_lub`.

No new capability or axiom is declared. `relational_lub` is the previously
studied closure of relational lifting under increasing limits; it is not a
class encoding interpreter preservation. Compared with the older guarded
route, this proof deliberately consumes stronger limit closure and does not
replace that weaker-assumption theorem.

The generic proof and all generic machine/scheduling endpoints are closed
under the global context (`Print Assumptions`). The FreeOmega specialization
inherits its existing backend laws, including their existing logical
dependencies; it does not claim those instances are axiom-free.

`Interp/FreeOmega/Unrestricted.v` is one application of the generic theorem.
Its native premises are SemanticMeasure, CoreLaws, AELift, CouplingAE,
CountableAE, and SemanticOmega operations, **not native omega completeness**.
Both SubEnumQ and SubEnumR clients compile. MathComp direct is not claimed
to acquire unconditional arbitrary-handler preservation: its required
relational-lub certificate remains a separate mathematical obligation.

## Why this proof is not circular

The proof uses an internal two-phase configuration, not a new program syntax
or probability model:

```
SourceConfig t
   -- complete source frontier, selected Vis e k -->
HandlerConfig (handler e) k
   -- handler Ret x --> SourceConfig (k x)
   -- handler Vis f c --> target visible head
```

Related Source configurations carry **source** peutt evidence. Related Handler
configurations use the same active handler tree and pointwise source-related
continuations. In particular, handler return is an INTERNAL transition:
the proof never assumes target peutt immediately after an eliminated event.
Arbitrarily many such transitions are resolved by finite kernel induction
followed by relational-lub closure.

Only an actual target `Vis` releases a target stable head. At that point its
remaining handler computation is paired by reflexivity and its source
continuation by `interp_bisim_candidate`, inside the established heterogeneous
`bind_upto_closure`. This is the visible guard required by the existing
coinductive proof, not a condition imposed on every handler execution.

## The machine really implements the existing interp

Relational simulation alone would not suffice. Two separate scheduling
proofs connect the machine to the unchanged `PTree.interp`.

`HandlerMachineScheduling.v` defines the physical one-native-step kernel and
proves, in approximation order, for each configuration `c`:

```
physical(n,c) <= actual-interp(n,c) <= physical(2*n+2,c).
```

The extra physical handler-return transition is silent. Directed cofinality
therefore gives the exact same complete hitting witnesses.

`HandlerMachineAcceleration.v` handles complete-frontier acceleration.
`grid(n,m,c)` allows `n` phase changes and uses `m` native steps for each
phase's frontier. Its checked finite bounds are:

```
grid(n,m,c) <= physical((n+1)*(m+1),c)
physical(n,c) <= grid(n,n,c).
```

Both coordinates are increasing. Diagonal bind continuity proves that the
inner limit is the complete-phase machine at fixed outer fuel. Fubini then
turns its complete outer limit into the diagonal `grid(n,n,c)`. The finite
bounds and directed cofinality connect this diagonal back to physical
execution and hence to `interp`.

This never uses `sem_eq -> sem_le` (which would be unsound for the observable
FreeOmega quotient). Even the associativity needed for phase unfolding is
derived specifically for finite native-generated frontiers, rather than
postulated for arbitrary frontier measures.

Finally `handler_vis_fusion` obtains actual interpreted hitting witnesses
from this scheduling proof, couples them by the machine relation, and applies
the existing `peutt_interp_of_vis_fusion`. Neither fusion nor its adequacy is
assumed. The `Proper` theorem is available for explicit local registration;
no global search hints or instances are added.

## Checked clients and remaining work

The regression uses ITree's standard `readerE` with genuine internally
returning and forwarding branches, heterogeneous results, infinitely many
eliminated requests, and real `setoid_rewrite`. A second handler mixes
positive returning mass with divergence; an independent SubEnumR client
instantiates the same completion theorem. Import-boundary checks precede
all backend imports.

This theorem alone does not establish State preservation: `run_state` carries
an evolving state, whereas this theorem interprets a fixed handler. The later
[state-indexed proof](STATE_PRESERVATION.md) supplies that result separately.
[StateT-fold commutation](STATE_FOLD.md), [single-draw rational sampling](RATIONAL_TICKETS.md)
and the [extracted rewrite example](STATE_REWRITE.md) are also complete.
The subsequent [runner distribution theorem](RUNNER_DISTRIBUTION.md) proves
the ideal conditional probability bridge, not PRNG correctness. See the
[current status and follow-up queue](EFFECTS_EXECUTION.md#current-status);
the verification below records this stage, not a later rerun.

## Verification boundary

`audit_handler_machine.py` freezes all 340 existing theory modules byte for
byte, allowing only the six sorted aggregate imports. Existing mainline,
MathComp, and 44-endpoint effects/execution snapshots remain unchanged. The
new 27-endpoint snapshot records elaborated types and logical assumptions,
with the existing whitelist and stronger axiom-free checks for generic proofs.
Mutation tests cover missing adequacy, missing finite bounds, invented
capabilities, source changes, backend leakage, and checker bypass.

Local verification completed: full `dune build` including AllImports and the
extracted executable, 202 Python tests, architecture/source audits, the
27-endpoint compiled audit, all 465 unchanged mainline contracts, all 44
unchanged operational contracts, and a joint six-module `coqchk -norec` all passed.
CI is intentionally not used. Targeted `coqchk -norec` checks the selected new safe module bodies, trusting
dependencies; it is not a whole-library recursive kernel audit and does not
include either Gate M module.
