# Formalization of Random Behavior for Interaction Trees

## Introduction

The current development contains a measure-parametric weak probabilistic
bisimulation in `theories/Eq/PWeakAbstract.v`.

Its probability interface is split into:

- `MeasureInterface`, providing return, bind, extensional equality,
  almost-everywhere predicates, and relational lifting;
- algebraic law packages for relation lifting, a.e. bind, and frontier
  uniqueness;
- `Enum_MeasureInterface`, the finite weighted-enumeration instance.  Its
  almost-everywhere predicate ignores zero-mass entries.

The relation `apweak` collapses finite `Tau`/probability prefixes to a
distribution of stable `Ret`/`Vis` heads.  It is proved reflexive, symmetric,
and transitive; see `PWeakAbstractTrans.v` for the `Equivalence` instance.

`apweak` is intentionally divergence-sensitive outside finite frontiers.
Consequently unrestricted monadic bind is not a congruence: a Dirac
probability node is equivalent to its return, but binding both programs to an
infinite `Tau` loop exposes the probability node again.  The mechanized
counterexample is `unrestricted_bind_congruence_fails` in
`PWeakFrontierExamples.v`.  Constructor-level bind rules and productive
examples are provided instead.

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
