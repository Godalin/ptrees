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
       -> probabilistic_eutt / ≈ₚ (relational reasoning)
       -> finite interaction observations / Prₜ[t | pattern] (quantitative)
```

The generic public facade is `Eq/ProbabilisticSemantics.v`.  It imports its
implementation dependencies without transitively exporting their historical
short names, then exposes the curated semantic vocabulary and endpoint laws.
PTree has one public behavioral equivalence: `probabilistic_eutt`, written
`t ≈ₚ u` (or `t ≈ₚ[RR] u`).  It is the greatest fixed point obtained by coupling the
stable-hitting behaviors of the two trees and recursively relating visible
continuations.  Its definition has no Tau, Prob, Bind, Iter, or certificate
constructor; the corresponding equations are derived laws.

`frontier_certificate` (compatibility name `frontier`), `pstructural`, and
`pstrong` belong to mechanization infrastructure.  The first is a
syntax-directed certificate system for proving stable-hitting facts;
`pstructural` is the lockstep relation used to establish structural equations;
and `pstrong` is a syntax-sensitive comparison baseline.  None is a competing
public behavioral semantics.  The coinductive layers use `coq-coinduction`;
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
`probabilistic_eutt_preserves_finite_trace_query` shows that `≈ₚ` preserves
every such finite cylinder without fixing the generic
theory to Enum, MathComp, rationals, or reals.  Continuation obligations hold
almost everywhere, so zero-mass branches need no artificial trace witness.
On backends with the order/omega laws needed to construct every complete
hitting limit, `finite_trace_query_exists` and
`finite_trace_query_unique_up_to_coupling` make the semantics well-defined.
The choice-based `finite_trace_sem` (public wrapper
`finite_interaction_sem`) packages a representative, and
`probabilistic_eutt_preserves_finite_trace_sem` is its extensional soundness
theorem.  Generic witness independence is stated as diagonal coupling;
backends may reflect that coupling to their own semantic equality.
`Eq/ProbabilisticTraceSubEnum.v` is the bounded paper-facing concrete
projection.  It defines `Prₛ[t | tr] = p` using an Enum expectation of a
`FreeOmega SubEnum`
representative coupled to a valid query, without pretending that the
choice-selected `finite_trace_sem` representative is executable.  The
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

`Prob/MeasureIteration.v` defines finite absorbing approximants and their
omega limits.  `meas_iter_ast` adds totality of that limit.  The maintained
FreeOmega backend supplies the support-aware omega, AE, coupling, diagonal,
and Fubini laws needed by arbitrary eventful PTree programs.  Finite programs
and unbounded AST programs therefore use the same semantics; bounded chains
are simply chains that stabilize early.

`Examples/VonNeumannUnbounded.v` proves the analytic convergence and AST
certificates for the genuinely unbounded biased-coin extractor.
`Examples/OperationalVonNeumann.v` interprets those certificates through
stable hitting and proves the canonical endpoint
`von_neumann_third_equivalent_to_fair`.
`Examples/InteractiveVonNeumannService.v` places the extractor between an
infinite sequence of request/reply events and proves
`interactive_von_neumann_service_equivalent` using guarded `Vis` matching and
coinduction up to `≈ₚ`.

The rational and Bernoulli source files likewise contain program definitions
and analytic certificates only.  Their maintained behavioral endpoints are
`probabilistic_eutt_binary_rational_coin_direct`,
`probabilistic_eutt_biased_to_rational_coin_direct`, and
`probabilistic_eutt_third_to_two_fifths_direct` in the corresponding
`Operational*` files.  The superseded `PWeak*` modules and
`apweak`/`auweak`/`auequiv` endpoints have been removed.

The underlying raw `Enum` `meas_eq` is extensional: two enumerations are equal when
every outcome has the same accumulated mass.  Raw list equality is exposed
separately as `enum_repr_eq`.  In particular, reordering entries, duplicating
an outcome, or splitting its mass does not change the measure.  The regression
file `Examples/EnumMeasureRegression.v` checks these cases together with
Dirac elimination and nested-probability flattening.  `SubEnum` reuses this
extensional theory while carrying the missing total-weight bound;
`Examples/SubEnumRegression.v` checks bind closure and rejects the legacy
weight-two flip.

The MathComp Analysis backend now supplies the same foundational AE profile
as Enum: AE Kleisli extension, exact Dirac AE, countable AE, coupling AE, and
exact bind support decomposition.  Through the FreeOmega behavior layer these
instances derive omega AE, diagonal continuity, Fubini, mixed unit, and
nested-`Prob` flattening.  Coupling composition remains the explicit
`MathCompCouplingGluing` capability.  The compile-time matrix lives in
`Examples/BackendCapabilities.v`.  The maintained real binary-oracle example
is canonically bisimilar to a direct real Bernoulli sample.

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
`free_interp_vis_fusion`; `free_probabilistic_eutt_interp_of_vis_fusion`
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

If you do not want to use the local `opam` switch, you can manually install the dependencies above.
