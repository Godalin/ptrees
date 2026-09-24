# StateT and the execution fold

Baseline: `1cca4ca`. This increment closes the previously explicit
StateT/fold commutation obligation without changing the existing fold,
State interpreter, probability interfaces, or their instances.

## The mathematical assumption

`MonadIter` is an operation, not an iteration theory. `Core/IterationLaws.v`
therefore states ordinary **pure-map uniformity** as an explicit proposition:

```
map (h + id) (f i) ≈ g (h i)
--------------------------------
iter f i ≈ iter g (h i)
```

Here map is monadic bind followed by ret. This law contains no PTree, effect,
state interpreter, or probability notion. It is not a new class or global
instance and does not assert the desired commutation theorem as a premise.
The existing ITree `Eq1`, `Eq1Equivalence`, and `MonadLawsE` express the
ordinary monad equations and their congruence; these are reused, not copied.

## Generic theorem

`Interp/StateFoldFacts.v` makes the StateT iterator's loop state explicit:
`(state, source tree)`. Its result is `(state, result)`. The pure map

```
(s,t) ↦ run_state t s
```

commutes with one fold step by the monad laws. Get and Put update/inspect the
state and enter the next loop step; an unhandled Vis uses `handle`; native
Prob uses the independent `sample` algebra. Uniformity lifts this one-step
square to the full, potentially infinite computation:

```
fold_state handle sample t s
  ≈ fold handle sample (run_state t s)
```

`fold_run_state` is generic in the target monad and event/native families.
It requires no SemanticMeasure, FreeOmega, or probability capability. Its
proof is closed under the global context; its algebraic premises are visible
in its compiled signature. It does not assert equality of arbitrary target
implementations possessing only Monad/MonadIter operations.

## A real target, and a negative boundary

`Execution/ITreeFold.v` proves `itree_iteration_uniform` using ITree's existing
relational `eutt_iter'` theorem, with the graph of the pure map as the loop
invariant. Thus `itree F` supplies an actual checked target, not an assumed
model. The module also proves fold unfolding and Ret/Tau/Vis/Prob equations
up to `eutt`; Vis and Prob still call separate algebras.

The regression instantiates the generic theorem in ITree, including the
unbounded rational State counter and arbitrary (possibly effectful) sampling
algebras. It separately checks Get elimination.

It also constructs a deliberately bad `MonadIter option`: before returning
a one-step result it checks whether **all**, including unreachable, loop
states return immediately. A map from unit to the true Boolean state makes
the step square commute, but the target's unreachable false state prevents
iteration from returning. Therefore that operation is proved **not uniform**.
This negative example uses Coq's existing classical decision; it declares no
axiom. It prevents silently treating bare MonadIter as a lawful iterator.

## Boundaries and validation

No sampler-distribution theorem, peutt-to-arbitrary-fold preservation, or
exact control-flow equality is claimed. ITree equality here is `eutt`, which
ignores the administrative Taus introduced by iteration. The native rational
uniform-ticket sampler was subsequently proved in [Rational tickets](RATIONAL_TICKETS.md).
This does not prove a fold/runner correspondence. The separate
[runner probability bridge](RUNNER_DISTRIBUTION.md) now proves the conditional
finite law without using fold. See the [current roadmap](EFFECTS_EXECUTION.md#current-status) for the
remaining queue; the validation below records this stage's checks.

The audit freezes the preceding 357 theory modules and six existing contract
snapshots. Sixteen compiled contracts cover the new algebra, theorem, actual
model, local equations, and negative regression. Full build/AllImports,
15 focused tool tests, the new compiled contracts and unchanged standard
effect contracts passed. Joint four-module `coqchk -norec` passed; dependencies
are trusted, and this is not a whole-library or Gate M check. No CI,
environment change, or Gate M expansion.
