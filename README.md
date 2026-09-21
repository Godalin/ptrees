# PTree: Probabilistic Eventful Computations

## Introduction

PTree is an intensional representation of computations in which native
probability, potentially infinite internal computation, and observable event
sequences coexist.  Stable hitting extracts its extensional probabilistic
behavior: it absorbs internal `Tau` and `Prob` evolution until reaching a
stable `Ret` or `Vis` head, while preserving missing termination mass.

Native `Prob` is instantiated with a subprobability carrier.  The canonical
finite executable carrier is `SubEnum`, a finite nonnegative enumeration
whose total weight is proved at most one; the MathComp carrier is intrinsically
a subprobability kernel.  Raw `Enum` remains a compatibility representation
for arbitrary finite nonnegative weights and is therefore not, by itself, a
valid native-probability backend.  This distinction keeps Bayesian `score`
weights separate from probabilistic choice.
The generic boundary is recorded by `SemanticSubprobability`: raw Enum
supports its per-measure predicate and closure laws, whereas SubEnum and
MathComp additionally provide `SemanticSubprobabilityCarrierLaws`, certifying
that every inhabitant is admissible at a native probability node.

The public conceptual architecture has four layers and two semantic clients:

```text
PTree syntax (intensional representation)
  -> ptree_primitive_kernel
  -> stable_hitting / H(t) (extensional behavior)
       -> peutt / ≈ₚ (relational reasoning)
       -> finite interaction observations / Prₜ[t | pattern] (quantitative)
```

The generic public facade is `API/Generic.v`.  It imports its
implementation dependencies without transitively exporting implementation
names, then exposes the curated semantic vocabulary and endpoint laws.
PTree has one public behavioral equivalence: `peutt`, written
`t ≈ₚ u` (or `t ≈ₚ[RR] u`).  It is the greatest fixed point obtained by coupling the
stable-hitting behaviors of the two trees and recursively relating visible
continuations.  Its definition has no Tau, Prob, Bind, Iter, or certificate
constructor; the corresponding equations are derived laws.

Proofs may use the following strength hierarchy before promoting their result
to the canonical behavioral endpoint:

```text
pstruct  ⊆  pstrong  ⊆  peutt
```

`pstruct` matches the tree representation exactly; `pstrong` retains
lockstep control flow but permits coupled sampling measures.  Internal
`Tau`/`Prob` computation is handled by stable-hitting calculation laws,
not by another equivalence relation.  The FreeOmega realization supplies
the inclusions into `peutt`; it does not require native coupling recovery
for these structural inclusions.

`Eq/StableHittingComputation.v` provides constructor characterizations,
Prob decomposition, distribution-level Dirac/flatten laws, and
`peutt_iff_hitting`.  `Eq/FreeOmega/Hitting.v` adds exact output rewriting
and Prob/Dirac/flatten `iff` rules for the observable FreeOmega backend.
Generic probability algebra uses equality coupling; it does not silently
identify that with arbitrary backends' semantic equality.
RandomWalk proves `passage_unfold` by structural unfolding followed by
`peutt_prob` and Tau transparency, even when the residual continuations
perform unbounded retries.  Bind and fmap reuse behavioral congruence.

The former `pfinite` relation and its dedicated promotion/recovery modules
have been removed without compatibility aliases.  Internal execution
certificates remain only as proof tools for stable-hitting computation
and schedule adequacy; they do not define another program equivalence.
`THEORY_STATUS.md` records the retained clients and capability boundaries.

`frontier_certificate`, `pstruct`, and `pstrong` belong to
mechanization infrastructure.  The first is a
syntax-directed certificate system for proving stable-hitting facts;
`pstruct` is the lockstep relation used to establish structural equations;
`pstrong` permits coupled probability nodes.  None is a competing public behavioral semantics.  The
coinductive layers use `coq-coinduction`;
Paco remains only an inherited ITree build dependency.

The framework is not limited to samplers returning a final value.  The
quantitative layer measures finite dependent-event cylinder patterns, and the
interactive Von Neumann case study proves the concrete two-event pattern
`Request; Reply(true)` has probability `1/2` despite an unbounded internal
retry loop.

`Eq/ProbabilisticTrace.v` provides measure-valued stable-head, next-event,
and finite interaction-prefix queries.  A dependent event selector both
recognizes an event and supplies the environment response used to enter its
continuation; a list of selectors is therefore a
`finite_interaction_pattern`, not necessarily one concrete trace.  Singleton
selectors represent ordinary concrete traces.
`peutt_preserves_finite_interaction_query` shows that `≈ₚ` preserves
every such finite cylinder without fixing the generic
theory to Enum, MathComp, rationals, or reals.  Continuation obligations hold
almost everywhere, so zero-mass branches need no artificial trace witness.
On backends with the order/omega laws needed to construct every complete
hitting limit, `finite_interaction_query_exists` and
`finite_interaction_query_unique_up_to_coupling` make the semantics well-defined.
The choice-based `finite_interaction_sem` packages a representative, and
`peutt_preserves_finite_interaction_sem` is its extensional soundness
theorem.  Generic witness independence is stated as diagonal coupling;
backends may reflect that coupling to their own semantic equality.
`Eq/Backend/ProbabilisticTraceSubEnum.v` is the bounded paper-facing concrete
projection.  It defines `Prₛ[t | tr] = p` using an Enum expectation of a
`FreeOmega SubEnum`
representative coupled to a valid query, without pretending that the
choice-selected `finite_interaction_sem` representative is executable.  The
theorem `subenum_finite_interaction_probability_range` proves every such
number lies in `[0,1]`.  The existing raw-Enum projection is retained for
compatibility with the current interactive case studies while they are
migrated to the bounded carrier; its numeric result is a finite weight unless
the program's node measures are separately shown subprobabilistic.  The
interactive Von Neumann example currently proves the compact raw-Enum endpoint
`Prₜ[von_neumann_service | request_true_reply_trace] = 1/2`.
This is prefix-satisfaction/cylinder semantics, not a pushforward trace
distribution.  The API does not claim an infinite-trace sigma-algebra or a general
expectation-transformer calculus.

### Unbounded stable hitting

`Prob/Interface/MeasureIteration.v` defines finite absorbing approximants and their
omega limits.  `meas_iter_ast` adds totality of that limit.  The maintained
FreeOmega backend supplies the support-aware omega, AE, coupling, diagonal,
and Fubini laws needed by arbitrary eventful PTree programs.  Finite programs
and unbounded AST programs therefore use the same semantics; bounded chains
are simply chains that stabilize early.

`Examples/BernoulliFactory/VonNeumannUnbounded.v` proves the analytic convergence and AST
certificates for the genuinely unbounded biased-coin extractor.
`Examples/BernoulliFactory/OperationalVonNeumann.v` interprets those certificates through
stable hitting and proves the canonical endpoint
`von_neumann_third_equivalent_to_fair`.
`Examples/InteractiveVonNeumann/InteractiveVonNeumannService.v` places the extractor between an
infinite sequence of request/reply events and proves
`interactive_von_neumann_service_equivalent` using guarded `Vis` matching and
coinduction up to `≈ₚ`.

`Examples/RandomWalk.v` studies an infinite-state loop: with probability
`2/3`, decrement the height and increment a streak; otherwise increment the
height and reset the streak.  Starting from `(1,0)`, it stops at height zero.
`run_split` factors a descent through an intermediate level using `pstruct`,
and `passage_unfold` proves the genuine `peutt` renewal equation
`D_y ≈ₚ Prob coin (fun down => if down then Ret (y+1) else D_0 >>= D)`.
`run_as_successive_passages` extends the decomposition to any initial
height, as a finite bind composition of unbounded one-level passages.
`random_walk_bind` makes the normalization usable in arbitrary client
continuations.  The full-state observation proof reuses the passage proof
through `ptree_hitting_observes_pstruct`; `random_walk_outputs_expect`
expresses the joint law as deterministic pushforward along `n ↦ (0,n)`.
`random_walk_closed_form` proves native stable-hitting AST and the normalized
joint output law `Pr[(0,n)] = 2/3^n` for `n >= 1` (zero elsewhere).
Finite observations are connected directly to the source's primitive kernel;
a rational contraction bound proves their limits without a random-walk
library or an additional measure axiom.  This is an output-distribution
endpoint, **not** a claim of `peutt` equivalence to a countably supported
distribution node or a geometric sampler.

`Examples/MixedHeadProtocol.v` is the canonical mixed-head bisimulation
example. A hidden-state implementation receives a Boolean challenge, samples
independent bits r (fair), s (P(true)=3/4), and h (fair). It either returns
c xor s or publishes it in a Reply, whose Boolean acknowledgement selects
the next hidden state: h on true, r on false. The fresh bit h affects only
the continuation. The specification
chooses among `Stop(false)`, `Stop(true)`, `Continue(false)`, and
`Continue(true)` with weights `(1/8,3/8,1/8,3/8)` for challenge false
and `(3/8,1/8,3/8,1/8)` for challenge true. It forgets the hidden state
but retains the public challenge. An explicit nonuniform eight-to-four coupling
forgets h and adds its two preimage masses for each abstract outcome.
The eight sampled atoms yield six concrete stable head forms: two returns
(h is discarded) and four Reply heads (two continuations per label).
The coupling merges each pair of Reply heads into one specification head.
A two-phase relation closes
all response-dependent continuations using plain
`peutt_coinduction` (no up-to closure). The theorem
`masked_protocol_equivalent` holds for either initial hidden bit.
The bounded backend is `SubEnum`, with intrinsic `probabilistic_ptree`
certificates. `masked_challenge_true_reply_probability` proves that the
pattern `[Challenge(c); Reply(true)]` has probability `3/8` when c=false
and `1/8` when c=true: the environment changes the observable probability
law, while return mass rejects the still-incomplete prefix. This example
explains the bisimulation definition itself; the Factory demonstrates
composition, and the VN service retains its role as unbounded internal
sampling between interactions.

The rational and Bernoulli source files likewise contain program definitions
and analytic certificates only.  Their maintained behavioral endpoints are
`peutt_binary_rational_coin_direct`,
`peutt_biased_to_rational_coin_direct`, and
`peutt_third_to_two_fifths_direct` in the corresponding
`Operational*` files.  The superseded `PWeak*` modules and
`apweak`/`auweak`/`auequiv` endpoints have been removed.

`Examples/BernoulliFactory/BernoulliFactoryComposition.v` exposes the compositional route.
`factory_with_sampler sampler q` accepts a Boolean sampler;
`peutt_factory_sampler_congr` preserves equivalence of closed
samplers using bind and eventless iteration congruence. The parametric
`peutt_factory_vn_fair` proves the VN sampler equivalent to a
direct fair coin. `peutt_factory_fair_direct` proves the fair
factory correct, and `peutt_factory_vn_direct` combines these
results explicitly by transitivity. Neither example-specific support class is
required on this route: the VN support is proved directly, and the binary
limit support follows from increasing finite approximations. Source weights
are nonnegative rationals summing to one with positive product; the target is
any rational in `[0,1]`, including the endpoints. Independently verified VN
and standard-binary components live in `OperationalBernoulliFactory.v`;
`BernoulliFactoryComposition.v` contains their algebraic composition.

`Examples/BernoulliFactory/BernoulliFactoryProbability.v` separately certifies the executable
raw `Enum` programs as `probabilistic_ptree`: normalized source weights make
the VN sampler well formed, and `probabilistic_factory_with_sampler` lifts
any sampler's probability contract through the entire Factory loop. This
contract needs neither source nondegeneracy nor termination. Raw Enum is the
executable representation; the certificates establish membership in its
subprobabilistic fragment.

`Prob/Backend/EnumSupport.v` proves AE continuity for increasing, convergent Enum
chains over outcomes with decidable equality, and proves that absorbing
iteration approximations are increasing.
`Prob/FreeOmega/FreeOmegaSupport.v` transports a concrete observation coupling back to
high-universe support when both observations preserve and reflect AE.
Observation equality or injectivity alone is insufficient: the disappearing
atom regression in `FreeOmegaMeasureEnumAudit.v` remains rejected.

The underlying raw `Enum` `meas_eq` is extensional: two enumerations are equal when
every outcome has the same accumulated mass.  Raw list equality is exposed
separately as `enum_repr_eq`.  In particular, reordering entries, duplicating
an outcome, or splitting its mass does not change the measure.  The regression
file `Regression/Backend/EnumMeasureRegression.v` checks these cases together with
Dirac elimination and nested-probability flattening.  `SubEnum` reuses this
extensional theory while carrying the missing total-weight bound;
`Regression/Backend/SubEnumRegression.v` checks bind closure and rejects the legacy
weight-two flip.

The MathComp Analysis backend now supplies the same foundational AE profile
as Enum: AE Kleisli extension, exact Dirac AE, countable AE, coupling AE, and
exact bind support decomposition.  Through the FreeOmega behavior layer these
instances derive omega AE, diagonal continuity, Fubini, mixed unit, and
nested-`Prob` flattening.  Coupling composition remains the explicit
`MathCompCouplingGluing` capability.  The compile-time matrix lives in
`Regression/Backend/BackendCapabilities.v`.  The maintained real binary-oracle
example is canonically bisimilar to a direct real Bernoulli sample under its
explicit `MathCompOracleSupportLaws` and coupling-gluing premises.

## Repository guide

The interpretation theory through Stage 4 is accepted at `ec96b90` and
frozen. Current work is the staged
[repository architecture and assumption cleanup](docs/ARCHITECTURE_CLEANUP.md),
with Gate A accepted at `2258907` and Gate B accepted at `20e6ff2`. Gate B implements the
[ownership boundaries and module splits](docs/ARCHITECTURE_MIGRATION.md).
The small [Examples follow-up](docs/EXAMPLES_FOLLOWUP.md) renames the
application directory without changing its programs or proofs; Gate C has
not started.
The [current inventory](docs/ARCHITECTURE_AUDIT.md) checks actual dependency
directions; the [current capability audit](docs/CAPABILITY_CURRENT.md)
compares 25 compiled endpoint signatures against the frozen
[Gate A baseline](docs/CAPABILITY_BASELINE.md). Capability minimization
and the final whole-library kernel audit remain separate gates.

Ordinary clients can import the curated entry points:

```coq
From PTree Require Import PTree.      (* syntax and canonical equational API *)
From PTree Require Import Semantics.  (* transition and MDP comparison API *)
From PTree.API Require Import SubEnum. (* optional concrete probability adapter *)
```

`Core/` owns syntax; `Prob/{Interface,FreeOmega,Backend,Legacy}/` separates
measure interfaces, the canonical model, concrete realizations and legacy
adapters. `Eq/` owns stable hitting and equality; `Eq/Internal/` holds proof
machinery. `Semantics/` owns independent comparison semantics. `Interp/`
owns interpretation preservation, with FreeOmega-qualified theory distinct
from concrete endpoints. `API/` assembles these layers without bulk exports.
Experts may import implementation modules explicitly. Paper-facing programs
form four groups:

- [MixedHeadProtocol](theories/Examples/MixedHeadProtocol.v): the flagship
  mixed Ret/Vis, whole-continuation coupling example;
- [RandomWalk](theories/Examples/RandomWalk.v): infinite-state descent,
  compositional equations and an analytic joint output law;
- [InteractiveVonNeumann](theories/Examples/InteractiveVonNeumann/):
  unbounded internal sampling between infinitely many interactions;
- [BernoulliFactory](theories/Examples/BernoulliFactory/):
  sampler correctness, replacement and composition, including the shared
  rational/real Bernoulli and ordinary Von Neumann proofs.

`Regression/{Semantics,Probability,Backend,Infrastructure}/` contains
theorem regressions, negative examples, capability checks and proof-tool
clients, not additional paper-facing case studies. In particular, the
2×2 strictness witness belongs to the semantic comparison regressions.
Its [two-round interpretation experiment](docs/INTERP_COMPOSITIONALITY.md)
also proves that response-wise transition bisimulation is not preserved by
arbitrary effectful interpretation.
For peutt, [semantic visible guarding](theories/Interp/FreeOmega/Guarded.v)
now suffices: `peutt_interp_guarded` preserves equivalence through handlers
whose complete first behavior is almost everywhere visible, allowing
internal probability and divergence. The same two-round handler therefore
preserves peutt even though it does not preserve transition bisimulation.
For transition bisimulation, [atomic interpretation](theories/Interp/FreeOmega/Atomic.v)
now provides a stronger sufficient contract: a response-preserving event
permutation, with complete Dirac hitting at one visible head and then at
the returned response. `tree_trans_bisim_interp_atomic` allows internal
computation but does not claim preservation for event merging or general
multi-interaction handlers.
For the MDP fragment, [MDPInterp](theories/Interp/FreeOmega/MDP.v) derives
`mdp_state` preservation for effect refinement `E -> F` from a local
stable-head handler contract. Its guarded route transports source
transition bisimulation to the target signature. The homogeneous `E -> E`
atomic profile satisfies it on SubEnum/FreeOmega, using a proved
totality-under-mapping lemma. Thus interpretation retains the fragment
where peutt and transition bisimulation coincide; no MDP reconstruction or
new interpretation semantics is introduced.

[THEORY_STATUS.md](THEORY_STATUS.md) is the current theorem/capability map,
including raw-tree transition comparison and MDP-fragment coincidence.
[The layout audit](docs/LAYOUT_AUDIT.md) records module moves, imports,
reachability and the retained internal infrastructure's clients.
[Local validation](docs/LAYOUT_VALIDATION.md) records the layout checks;
[joint universe consistency](docs/UNIVERSE_CONSISTENCY.md) explains the
subsequent two-level regression repair and the full-library import guard.
Finite-internal/kernel infrastructure is grouped under `Eq/Internal/`;
it is not another behavioral relation. The universe representation probes
now live in `Regression/Infrastructure`, not an active Experimental layer.

## Artifact claims

The reproducible artifact currently targets Coq 8.20 (CI pins 8.20.1); the
package metadata deliberately excludes Coq 9 pending a separate Stdlib and
dependency migration.

The maintained artifact establishes:

- one canonical weak probabilistic equivalence `≈ₚ`, including reflexivity,
  symmetry, transitivity, Tau weakening, probability congruence, and bind
  congruence;
- a sound heterogeneous coinduction-up-to-bind rule;
- one semantics for bounded and genuinely unbounded AST computation;
- eventful iteration, interpretation/translation laws, and quantitative
  next-event observations;
- SubEnum and MathComp Analysis subprobability instances, plus a legacy raw
  Enum weighted instance; executable rational examples are being migrated
  to the bounded carrier without changing the generic behavioral theory.

Two stronger statements are intentionally not claimed.  The remaining
arbitrary-effectful-handler premise is now isolated as
`interp_vis_fusion`; `peutt_interp_of_vis_fusion`
derives full preservation once that one collapsed handled-`Vis` segment is
supplied.  Ordinary up-to-bind compatibility cannot discharge it without an
unguarded recursive use after the handler returns internally.  Likewise,
the exact no-`Prob` correspondence with ITree `eutt` still requires the
pure-tree hitting classification and dependent visible-head inversion
described in [`THEORY_STATUS.md`](THEORY_STATUS.md).  The existing generic
measure interface is deliberately not strengthened with representation-
specific separation axioms merely to state that correspondence.

## Meta

- Author(s):
  - Linyu Yang

## Building Instructions

### Obtaining the project

```sh
git clone git@github.com:Godalin/ptrees.git
cd ptrees
```

### Setting up the environment

Create a local `opam` switch, activate it, and install the dependencies:

```sh
opam switch create . 4.14.2 \
  --repos default,coq-released=https://coq.inria.fr/opam/released
eval $(opam env)
opam install . --deps-only --with-test
```

### Build the project

Run

```sh
dune build
```

to build the theories.

### Dependencies

The main dependencies, installed automatically by opam, are:

- `coq-ext-lib`
- `coq-coinduction`
- `coq-itree`
- `coq-paco` (through the ITree ecosystem)
- `coq-mathcomp-algebra`
- `coq-mathcomp-analysis`
- `coq-mathcomp-reals-stdlib` (standard real model for native coupling reflection)

If you do not want to use the local `opam` switch, you can manually install the dependencies above.
