# Formalization of Random Behavior for Interaction Trees

## Introduction

PTree has one maintained weak/extensional probabilistic behavioral
equivalence: `probabilistic_eutt`, written `t ≈ₚ u` (or `t ≈ₚ[RR] u` for a
heterogeneous return relation).  It compares complete subprobabilistic
stable-hitting limits through couplings of stable `Ret`/`Vis` heads.
Internal `Tau` and `Prob` computation are abstracted by the hitting semantics;
missing termination mass remains observable.

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

Create a local `opam` switch and install the dependencies, and activate the switch:

```sh
opam switch create ./ --repos default,coq-released=https://coq.inria.fr/opam/released --deps-only
eval $(opam env)

# update the dependencies
opam install ./ --deps-only
```

### Build the project

Run

``` sh
dune build
```

to build the theories.

### Dependencies

We list the dependencies here, although are not needed to be installed manually if you use the local `opam` switch approach:
- `coq-ext-lib`
- `coq-coinduction`
- `coq-itree`
- `coq-mathcomp`

If you do not want to use the local `opam` switch, you can manually install the dependencies above.
