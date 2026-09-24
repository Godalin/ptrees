# PTree: Probabilistic Eventful Computations

## Introduction

PTree is an intensional representation of computations in which native
probability, potentially infinite internal computation, and observable event
sequences coexist.  Stable hitting extracts its extensional probabilistic
behavior: it absorbs internal `Tau` and `Prob` evolution until reaching a
stable `Ret` or `Vis` head, while preserving missing termination mass.

Native `Prob` is instantiated with a subprobability carrier.  The canonical
finite executable carrier is `SubEnumQ`, a finite nonnegative enumeration
whose total weight is proved at most one; `SubEnumR R` provides finite real
weights with the same validity bound. Both use the shared `FiniteSubdist`
record, instantiated at ordinary `rat` or real scalars. `EnumQ = FiniteEnum rat`
represents arbitrary finite nonnegative weights and is therefore not, by itself, a
valid native-probability backend.  This distinction keeps Bayesian `score`
weights separate from probabilistic choice.
Nonnegativity and the mass bound belong to the containers, not scalar
subtypes. The old `nnQ` representation is isolated in `Prob/Legacy`; Q-to-R
transport uses the shared scalar-map construction. See the
[finite-backend consolidation](docs/FINITE_BACKEND_CONSOLIDATION.md).
The generic boundary is recorded by `SemanticSubprobability`: raw EnumQ
supports its per-measure predicate and closure laws, whereas SubEnumQ, SubEnumR
and the native MathComp kernel provide `SemanticSubprobabilityCarrierLaws`, certifying
that every inhabitant is admissible at a native probability node.

The maintained complete PTree behavioral backends are
`SubEnumQ -> FreeOmega SubEnumQ` and `SubEnumR R -> FreeOmega (SubEnumR R)`.
MathComp supplies a separate discrete kernel/measure model for native analytic
results and native joint witnesses. An explicitly universe-unchecked
`MN = MF = MathCompKernelMeasure R` assembly is maintained separately as Gate M.
Native order, omega continuity, diagonal/Fubini and relational bind are proved
with normal universe checking. The isolated direct layer proves general hitting
existence and eventful bind congruence, with unbounded/nested retry regressions.
It is **not** a third fully universe-checked backend. There is no MathComp-plus-
completion workaround. See [direct MathComp trust boundary](docs/MATHCOMP_DIRECT.md).

The public conceptual architecture has four layers and two semantic clients:

```text
PTree syntax (intensional representation)
  -> ptree_primitive_kernel
  -> stable_hitting / H(t) (extensional behavior)
       -> peutt / ≈ₚ (relational reasoning)
       -> finite interaction observations / Prₜ[t | pattern] (quantitative)
```

`PTree.v` exports program definitions, `Eq.v` exports relation owners and their
notation modules, and `PTreeFacts.v` aggregates the actual reasoning modules.
There is no alias-based `API/` layer. Canonical behavioral profiles live in
`Eq/Canonical` and explicit `Eq/Backend` adapters.
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
theory to EnumQ, MathComp, rationals, or reals.  Continuation obligations hold
almost everywhere, so zero-mass branches need no artificial trace witness.
On backends with the order/omega laws needed to construct every complete
hitting limit, `finite_interaction_query_exists` and
`finite_interaction_query_unique_up_to_coupling` make the semantics well-defined.
The choice-based `finite_interaction_sem` packages a representative, and
`peutt_preserves_finite_interaction_sem` is its extensional soundness
theorem.  Generic witness independence is stated as diagonal coupling;
backends may reflect that coupling to their own semantic equality.
`Eq/Backend/ProbabilisticTraceSubEnumQ.v` is the bounded paper-facing concrete
projection.  It defines `Prₛ[t | tr] = p` using an EnumQ expectation of a
`FreeOmega SubEnumQ`
representative coupled to a valid query, without pretending that the
choice-selected `finite_interaction_sem` representative is executable.  The
theorem `subenumQ_finite_interaction_probability_range` proves every such
number lies in `[0,1]`.  The existing raw-EnumQ projection is retained for
compatibility with the current interactive case studies while they are
migrated to the bounded carrier; its numeric result is a finite weight unless
the program's node measures are separately shown subprobabilistic.  The
interactive Von Neumann example currently proves the compact raw-EnumQ endpoint
`Prₜ[von_neumann_service | request_true_reply_trace] = 1/2`.
This is prefix-satisfaction/cylinder semantics, not a pushforward trace
distribution.  The API does not claim an infinite-trace sigma-algebra or a general
expectation-transformer calculus.

### Unbounded stable hitting

`Prob/Interface/Iteration.v` defines finite absorbing approximants and their
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
The bounded backend is `SubEnumQ`, with intrinsic `probabilistic_ptree`
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
raw `EnumQ` programs as `probabilistic_ptree`: normalized source weights make
the VN sampler well formed, and `probabilistic_factory_with_sampler` lifts
any sampler's probability contract through the entire Factory loop. This
contract needs neither source nondegeneracy nor termination. Raw EnumQ is the
executable representation; the certificates establish membership in its
subprobabilistic fragment.

`Prob/Backend/EnumQ/Support.v` proves AE continuity for increasing, convergent EnumQ
chains over outcomes with decidable equality, and proves that absorbing
iteration approximations are increasing.
`Prob/FreeOmega/Support.v` transports a concrete observation coupling back to
high-universe support when both observations preserve and reflect AE.
Observation equality or injectivity alone is insufficient: the disappearing
atom regression in `Prob/Backend/EnumQ/FreeOmega/MeasureAudit.v` remains rejected.

The underlying raw `EnumQ` `meas_eq` is extensional: two enumerations are equal when
every outcome has the same accumulated mass.  Raw list equality is exposed
separately as `enumQ_repr_eq`.  In particular, reordering entries, duplicating
an outcome, or splitting its mass does not change the measure.  The regression
file `Regression/Backend/EnumQMeasureRegression.v` checks these cases together with
Dirac elimination and nested-probability flattening.  `SubEnumQ` reuses this
extensional theory while carrying the missing total-weight bound;
`Regression/Backend/SubEnumQRegression.v` checks bind closure and rejects the legacy
weight-two flip.

The MathComp Analysis backend now supplies the same foundational AE profile
as EnumQ: AE Kleisli extension, exact Dirac AE, countable AE, coupling AE, and
exact bind support decomposition, plus checked omega, diagonal/Fubini and
relational kernel-bind laws. Coupling composition remains the explicit
`MathCompCouplingGluing` capability.  The compile-time matrix lives in
`Regression/Backend/BackendCapabilities.v`. The direct real binary-oracle
analysis in `Examples/BernoulliFactory/RealBernoulliMathComp.v` is retained;
its MathComp--FreeOmega `peutt` frontend has been removed.

## Repository guide

The accepted interpretation theory and probability-domain soundness are frozen.
See [repository architecture](docs/ARCHITECTURE.md) for ownership and the
generic / FreeOmega / concrete-backend boundaries, and the
[current inventory](docs/ARCHITECTURE_AUDIT.md) for machine-checked dependencies.
The [external soundness account](docs/FREEOMEGA_SOUNDNESS.md) explains admissible
FreeOmega SubEnumQ, standard measures, general joint coupling and stable-hitting
adequacy. These validation modules are not imported by program reasoning.
The [generic validation layer](docs/GENERIC_QLIFT_VALIDATION.md) proves
native-parametric bounded-test/bidual soundness, instantiated by SubEnumQ and
SubEnumR. Actual external joint existence is a separate, model-specific
strengthening, not a behavioral backend requirement. The
[SubEnumR realization](docs/SUBENUMR_JOINT_REALIZATION.md) now closes that
strengthening for the finite-real completion as well as SubEnumQ. The
[three-layer policy](docs/ARCHITECTURE.md#three-layers-of-probability-reasoning)
distinguishes relational lifting, semantic joint witnesses and external joint
realization.
The [compiled contracts](docs/CONTRACTS.json) preserve 266 distinct owner/helper
and 199 soundness endpoints, including the original 25 capability probes.
The [module migration ledger](docs/PUBLIC_MODULES.md) accounts for every old
alias and the ten removed convenience contracts.
Stage-specific migration narratives and snapshots remain in git history.
The final whole-library kernel audit (Gate D) remains separate.

Ordinary clients can import the entry points:

```coq
From PTree Require Import PTree.      (* program construction only *)
From PTree Require Import PTreeFacts. (* relation notation and reasoning *)
From PTree Require Import Semantics.  (* transition and MDP comparison API *)
From PTree.Eq.Backend Require Import SubEnumQ. (* explicit canonical profile *)
```

`Core/` owns syntax; `Prob/{Interface,FreeOmega,Backend,Legacy}/` separates
measure interfaces, the canonical model, concrete realizations and legacy
adapters. `Prob/Backend/{Common,EnumQ,SubEnumQ,SubEnumR,MathComp}/` makes the native
carrier explicit; `Prob/FreeOmega/` stays generic in `MN`, while
`Prob/Backend/SubEnumQ/FreeOmega/` specializes that completion to SubEnumQ.
`Eq/` owns stable hitting and equality; `Eq/Internal/` holds proof
machinery. `Semantics/` owns independent comparison semantics. `Interp/`
owns interpretation preservation, with FreeOmega-qualified theory distinct
from concrete endpoints. Relation modules own `≡ₚ / ≃ₚ / ≈ₚ`, including their
heterogeneous forms. `Eq/Bind` owns the backend-independent heterogeneous
`peutt_bind`; FreeOmega and direct MathComp supply the same probability-level
order/selection laws. `peutt_bind_cofinal` is the lower-level explicit-scheduling
endpoint. `Eq/Algebra` provides the same generic bind/fmap `Proper` proofs to
both completion and direct-frontier clients; see the
[consumer extraction and local rewriting profiles](docs/GENERIC_ALGEBRA.md).
See [generic bind extraction](docs/GENERIC_BIND.md) and
[public module migration](docs/PUBLIC_MODULES.md).
Experts may import owners directly. Paper-facing programs
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
atomic profile satisfies it on SubEnumQ/FreeOmega, using a proved
totality-under-mapping lemma. Thus interpretation retains the fragment
where peutt and transition bisimulation coincide; no MDP reconstruction or
new interpretation semantics is introduced.

[THEORY_STATUS.md](THEORY_STATUS.md) is the current theorem/capability map,
including raw-tree transition comparison and MDP-fragment coincidence.
The [architecture inventory](docs/ARCHITECTURE_AUDIT.md) records maintained
modules and clients; [Cleanup B validation](docs/CLEANUP_B_VALIDATION.md)
records the consolidation and its check scope.
[Joint universe consistency](docs/UNIVERSE_CONSISTENCY.md) explains the
two-level regression repair and full-library import guard.
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
- SubEnumQ and SubEnumR complete probability backend instances, separate
  native MathComp Analysis results, and a legacy raw EnumQ weighted instance;
  executable rational examples are being migrated
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

For a new checkout, create a local `opam` switch and install the frozen CI
dependency profile. Do not recreate or upgrade an existing working switch.

```sh
opam switch create . ocaml-base-compiler.5.2.1 \
  --repos default,coq-released=https://coq.inria.fr/opam/released
eval $(opam env)
opam install ./.github/ci/ptree-ci.opam -y
opam install . --deps-only --with-test
python3 tools/check_ci_environment.py
```

The [CI profile](.github/ci/README.md) fixes the compiler and all recorded
dependency versions, including Dune 3.17.2 and Coq 8.20.1. It does not change the
library's general compatibility bounds or claim identical macOS/Linux system
environments.

### Build the project

Run

```sh
dune build
```

to build the theories.

### Executable probability programs

For **unbounded execution of an already proved sampler**, run:

```sh
opam exec -- dune exec extraction/unbounded/main.exe -- vn stats 10000 42
opam exec -- dune exec extraction/unbounded/main.exe -- direct stats 10000 42
```

These extract the existing Von Neumann retry program and the direct fair
sampler that it is proved `peutt`-equivalent to. Neither execution uses fuel.
The nested Bernoulli factory is also executable: use `factory` and
`factory-direct` in place of `vn` and `direct` to compare the proved
biased-coin-to-2/5 construction with direct Bernoulli(2/5) sampling.
See [unbounded simulation](docs/UNBOUNDED_SIMULATION.md) for single-run,
streamed replay, nontermination and trust boundaries. Simulation statistics
are not a PRNG or end-to-end OCaml correctness proof.

The bounded State examples remain available:

```sh
opam exec -- dune exec extraction/state-counter/main.exe -- replay 7 0 010
opam exec -- dune exec extraction/state-counter/main.exe -- seed 40 0 42 10
```

The program, state handler, rational interval selector and bounded runner are
extracted from Rocq. The first command returns counter value 2 with one unused
bit. See [effects and execution](docs/EFFECTS_EXECUTION.md) for the proved
operational contracts, completed handler and single-draw sampling proofs,
and the [finite runner probability correspondence](docs/RUNNER_DISTRIBUTION.md)
under an explicit history-conditional uniform entropy contract. This does not
verify PRNG fairness. The
[State rewrite example](docs/STATE_REWRITE.md) also extracts both sides of a
proved probability rewrite with general rational ticket sampling.

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
