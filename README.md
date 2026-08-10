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

### Unbounded almost-sure frontiers

The unbounded extension is split into three files:

- `Prob/MeasureIteration.v` defines the `n`-step absorbing submeasure of a
  Kleisli loop and defines its unbounded result relationally as an omega
  limit.  Runs which have not terminated within `n` steps contribute zero
  mass, so a purely divergent loop cannot be assigned an arbitrary result by
  coinduction.  `meas_iter_ast` additionally requires that the limit has total
  mass one.
- `Eq/PWeakUnbounded.v` adds `aufrontier`, whose iteration rule collapses a
  `PTree.iter` only after its finite approximants have a certified measure
  limit **and that limit has total mass one**, and defines the corresponding greatest-fixed-point relation
  `auweak`.  Reflexivity and symmetry are mechanized.
- `Prob/MeasureIterationEnum.v` instantiates limits for finite rational
  enumerations using convergence of the mass of every Boolean measurable
  set.  The limit is relational because `Enum` is not closed under arbitrary
  omega-limits: a limit may have infinite support or irrational weights.

`Examples/VonNeumannUnbounded.v` is the main unbounded regression test.  Its
source program repeatedly tosses a coin with weights `1/3` and `2/3` twice,
retries when the results agree, and returns a bit when they differ.  The
development proves that its `n`-step output is

```text
(1 - (5/9)^n) * fair
```

and proves `(5/9)^n <= 2/(n+2)`, hence convergence to the fair distribution.
The final theorem is:

```coq
Theorem von_neumann_third_equivalent_to_fair :
  auweak eq von_neumann_third direct_fair.
```

The same file also provides `von_neumann_correct_of_convergence`, a
parameterized program-level theorem for arbitrary bias weights `p` and `q`.
It isolates the only model-specific analytic obligation—convergence of the
absorbing iteration—from the coinductive weak-bisimulation proof.

The current `Enum` `meas_eq` is intentionally representation-sensitive
(pruned-list equality), while omega convergence is observational.  Therefore
there is no global `MeasureOmegaLaws Enum` instance claiming that
observationally equal limits have identical list representations.  Any future
transitivity theorem for raw `auweak` must either use an extensional measure
equality or state the required frontier-coherence law explicitly.

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
