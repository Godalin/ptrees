# Formalization of Random Behavior for Interaction Trees

## Introduction

The current development contains a measure-parametric weak probabilistic
bisimulation in `theories/Eq/PWeakAbstract.v`.

`Eq/PStrong.v` provides the corresponding strong baseline.  It matches
`Ret`, `Tau`, `Vis`, and `Prob` constructors in lockstep, while allowing two
probability nodes to be related through the abstract `ProbRelLift` interface.
It is proved reflexive, symmetric, and transitive directly with
`coq-coinduction`.  In contrast, `apweak` may collapse finite internal
`Tau`/probability prefixes and `auweak` additionally admits certified AST
omega iterations.

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
The probabilistic weak relations and their transitivity proofs use
`coq-coinduction` directly, including its enhanced `Chain` principle; no
project-level Paco adapter is used.  The Paco package remains a build
dependency because it is part of the surrounding ITree dependency stack.

`apweak` is intentionally divergence-sensitive outside finite frontiers.
Consequently unrestricted monadic bind is not a congruence: a Dirac
probability node is equivalent to its return, but binding both programs to an
infinite `Tau` loop exposes the probability node again.  The mechanized
counterexample is `finite_unrestricted_bind_congruence_fails` in
`FiniteBindCounterexample.v`; its statement is deliberately limited to the
finite compatibility relation and does not overclaim the same result for the
unified AST-aware relation.  Constructor-level bind rules and productive
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
  `auweak`.  Reflexivity and symmetry are mechanized directly.
- `Eq/PWeakUnboundedTrans.v` proves transitivity of raw `auweak` using
  extensional frontier coherence and coupling composition, and installs its
  `Equivalence` instance.  `Eq/PWeakUnboundedEquiv.v` retains `auequiv` only
  as a compatibility wrapper; the maintained theory does not rely on an
  artificial reflexive-symmetric-transitive closure.
- `Prob/MeasureIterationEnum.v` instantiates limits for finite rational
  enumerations using convergence of the mass of every Boolean measurable
  set.  The limit is relational because `Enum` is not closed under arbitrary
  omega-limits: a limit may have infinite support or irrational weights.
- `Prob/RatGeometric.v` proves an Archimedean contraction principle for
  rational retry probabilities.  In particular, every `0 <= r < 1`
  automatically admits a natural `K > 0` with `r <= K/(K+1)`, which yields
  an explicit bound tending to zero for `r^n`.

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

The same file also provides a parameterized proof stack for arbitrary input
bias weights `p` and `q`: `von_neumann_correct_of_convergence` isolates the
model-specific limit obligation, `von_neumann_correct_of_strict_retry`
discharges it from `0 <= retry < 1`, and
`von_neumann_correct_of_normalized_bias` derives all analytic premises from
the user-facing assumptions that the weights sum to one and their product is
strictly positive.  Thus the retry loop is genuinely unbounded, almost surely
terminating, and weakly equivalent to a direct fair toss for every
nondegenerate rational input bias.  The corresponding client-facing results
are `von_neumann_third_auequiv_fair` and
`von_neumann_auequiv_of_normalized_bias`.

The current `Enum` `meas_eq` is extensional: two enumerations are equal when
every outcome has the same accumulated mass.  Raw list equality is exposed
separately as `enum_repr_eq`.  In particular, reordering entries, duplicating
an outcome, or splitting its mass does not change the measure.  The regression
file `Examples/EnumMeasureRegression.v` checks these cases together with
Dirac elimination and nested-probability flattening.

The MathComp Analysis backend supports measure, bind, subprobability,
omega-limit, AST, and the universe-safe two-level unified frontier.  Coupling
composition remains the explicit `MathCompCouplingGluing` capability.  The
maintained real binary-oracle example is unified-weak-bisimilar to a direct
real Bernoulli sample.  The older real-valued Von Neumann and composed factory
clients remain experimental until migrated to the same two-level interface;
they are excluded from the default installed theory rather than presented as
maintained results.

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
