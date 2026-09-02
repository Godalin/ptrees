# PTree: Probabilistic Eventful Computations

## Introduction

PTree has one maintained weak/extensional probabilistic behavioral
equivalence: `probabilistic_eutt`, written `t ≈ₚ u` (or `t ≈ₚ[RR] u` for a
heterogeneous return relation).  It compares complete subprobabilistic
stable-hitting limits through couplings of stable `Ret`/`Vis` heads.
Internal `Tau` and `Prob` computation are abstracted by the hitting semantics;
missing termination mass remains observable.

The project is a semantic framework for computations in which native
probability, potentially infinite internal computation, and observable event
sequences coexist.  It is not limited to samplers returning a final value:
the quantitative query layer can measure stable visible-event classes, and
the interactive Von Neumann case study proves the protocol observation
`Request; Reply(true)` has probability `1/2` despite an unbounded internal
retry loop.

The semantic stack is:

```text
PTree.observe
  -> ptree_primitive_kernel
  -> stable_hitting_weak
  -> sem_lift over stable heads
  -> probabilistic_eutt (greatest fixed point)
```

`Eq/PStrong.v` remains the syntax-sensitive strong baseline.  It matches
`Ret`, `Tau`, `Vis`, and `Prob` constructors in lockstep through the abstract
probability lifting.  The weak canonical relation has no syntax constructors:
Tau laws, probability congruence, bind congruence, iteration certificates, and
coinduction rules are derived theorems.  Both layers use `coq-coinduction`;
Paco remains only an inherited ITree build dependency.

`Eq/ProbabilisticTrace.v` provides measure-valued stable-head, next-event,
and finite interactive trace-prefix queries.  A dependent event selector
both recognizes an event and supplies the environment response used to enter
its continuation.  `probabilistic_eutt_preserves_finite_trace_query` shows
that `≈ₚ` preserves every such finite cylinder without fixing the generic
theory to Enum, MathComp, rationals, or reals.  Continuation obligations hold
almost everywhere, so zero-mass branches need no artificial trace witness.
This API does not yet claim an infinite-trace sigma-algebra or a general
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

The current `Enum` `meas_eq` is extensional: two enumerations are equal when
every outcome has the same accumulated mass.  Raw list equality is exposed
separately as `enum_repr_eq`.  In particular, reordering entries, duplicating
an outcome, or splitting its mass does not change the measure.  The regression
file `Examples/EnumMeasureRegression.v` checks these cases together with
Dirac elimination and nested-probability flattening.

The MathComp Analysis backend supports measure, bind, subprobability,
omega-limit, AST, and the universe-safe two-level unified frontier.  Coupling
composition remains the explicit `MathCompCouplingGluing` capability.  The
maintained real binary-oracle example is canonically bisimilar to a direct
real Bernoulli sample.  The former one-level composed factory client was
removed; a future nested real factory must be rebuilt over the two-level
canonical iter/congruence API.

## Artifact claims

The maintained artifact establishes:

- one canonical weak probabilistic equivalence `≈ₚ`, including reflexivity,
  symmetry, transitivity, Tau weakening, probability congruence, and bind
  congruence;
- a sound heterogeneous coinduction-up-to-bind rule;
- one semantics for bounded and genuinely unbounded AST computation;
- eventful iteration, interpretation/translation laws, and quantitative
  next-event observations;
- Enum and MathComp Analysis instances, with executable rational examples
  and real-measure examples respectively.

Two stronger statements are intentionally not claimed.  Arbitrary effectful
handlers still require a stable-hitting-aware companion/fusion theorem after
an internally returning handler enters a recursive continuation.  Likewise,
the exact no-`Prob` correspondence with ITree `eutt` still requires the
pure-tree hitting classification and dependent visible-head inversion
described in [`THEORY_STATUS.md`](THEORY_STATUS.md).  The existing generic
measure interface is deliberately not strengthened with representation-
specific separation axioms merely to state that correspondence.

## Meta

- Author(s):
  - Linyu Yang
  - Yuchi Su

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
- `coq-relation-algebra`
- `coq-mathcomp-algebra`
- `coq-mathcomp-analysis`

If you do not want to use the local `opam` switch, you can manually install the dependencies above.
