# Return-only iteration and classical least fixed points

Frontier iteration conservatively extends ordinary absorbing Kleisli
iteration. The hypothesis is local to the program: each actual step has a
complete frontier `bind (K i) (ret o FHRet)`. The event signature itself
may be inhabited. The kernel `K : I -> MF (I + A)` may have missing mass,
infinite support, and unbounded internal computation in its implementation.
Neither almost-sure termination nor a finite native representation of its
limit is required.

## Generic compatibility

`Prob/Interface/KleisliIteration.v` defines

```text
Phi X i = bind (K i) [inl j => X j | inr a => ret a]
approx 0 i = zero
approx (S n) i = Phi (approx n) i
sem_iter K i out = sem_lub (approx · i) out
```

`Interp/ReturnIteration.v` proves:

- `iteration_summary_round_return_only`: summary round `n` is `sem_eq`
  to `map FHRet (approx (S n) i)`.
- `iteration_summary_return_only`: any summary witness and any `sem_iter`
  witness agree under `sem_eq`, after mapping the latter through `FHRet`.
- `iteration_summary_mixed_iter`: the same limit compatibility with the
  existing native-kernel `mixed_iter`, without changing its definition.
- `ptree_iter_return_only` and `ptree_iter_mixed_iter`: actual complete
  step certificates and a classical iteration witness yield an actual
  PTree iteration hitting witness equal to that mapped result.

The index shift is intentional. Frontier round zero already retains exits
from the complete first step; classical approximation zero is bottom.
The existing zero-prefix/cofinality law removes this shift at the limit.
The program theorems use generalized frontier adequacy: clients do not
provide a separate `ptree_iter_cofinal` proof.

Generic `sem_lub` is not assumed saturated in its output under `sem_eq`.
Consequently the program endpoint constructs a hitting witness and proves
its equality to the mapped classical result; it does not silently replace
the witness in the hitting predicate.

## What is genuinely a least fixed point?

`sem_iter_fixed_point` proves `X = Phi X` under `sem_eq` from existing
omega/diagonal laws. This alone is not leastness. For the endless-retry
kernel, a nonzero Dirac value is also a fixed point, while iteration from
bottom remains zero.

`sem_iter_least_fixed_point` additionally takes the ordinary upper-bound
and least-upper-bound properties of `sem_lub` as explicit hypotheses.
It proves both fixed-point inequalities and leastness among all pre-fixed
points. These hypotheses are not a new typeclass or a new global axiom,
and are **not asserted for the raw FreeOmega approximation order**.

Two concrete mathematical interpretations close this distinction:

1. `Prob/Backend/MathComp/Iteration.v` constructs `mathcomp_iteration` and
   proves its least-fixed-point property using existing native measure lub
   upper/least theorems. This mathematics is normally universe-checked and
   requires no coupling-gluing assumption. The actual recursive PTree
   client remains in the already authorized `MathComp` Gate M file;
   that client explicitly retains gluing for the generic CoreLaws algebra.
2. `Prob/Domain/Iteration.v` independently constructs `oval_iter` in the
   expectation domain and proves `oval_iter_fixed_point` and
   `oval_iter_least_prefixed`. It imports no PTree, FreeOmega or semantic
   interface. `Prob/FreeOmega/Validation/Iteration.v` proves that the
   canonical `FOLub` of classical approximants denotes this genuine lfp,
   for any native interpretation and denoted step kernels. In particular
   it proves that this formal iteration is modelable.

The second bridge is about the canonical `FOLub` representative. Applying
it to other quotient-equal witnesses additionally uses the existing
quotient validation hypotheses; the new theorem does not erase that
boundary or assume every raw FreeOmega term has a probability model.
No complete Elgot-monad axiom suite is claimed here.

## Regression and trust boundary

`Regression/Semantics/IterationFrontiers.v` checks an inhabited event
signature, arbitrary MF kernels, native compatibility, the finite index
shift, zero/missing mass, and endless retry with a nonleast fixed point.
`Regression/Probability/KleisliIteration.v` checks the independent domain,
safe MathComp leastness and a SubEnumQ loop's denotation/modelability.
`MathComp.return_only_lfp` connects actual PTree iteration to
the safe native lfp theorem using the same generic program theorem.

There are no changes to existing probability classes, FreeOmega relations,
canonical routing or checker-relaxation permissions. Compiled signatures
and logical dependencies are recorded in the existing generic-algebra
contract suite; no new audit subsystem is introduced.

## Local validation

- Full `opam exec -- dune build -j 2`, including safe AllImports and extraction.
- 141 tool tests; architecture, API surface and soundness source checks.
- All 465 main contracts, 103 previous safe generic-algebra contracts and
  four previous generic Gate M contracts are unchanged. Seventeen new safe
  endpoints bring the generic suite to 120; one new direct endpoint brings
  its separate Gate M suite to five. The original 43 MathComp
  contracts also remain unchanged.
- All eight new recorded generic interface/program endpoints are closed
  under the global context. The model endpoints inherit only existing
  choice/extensionality dependencies, within the established whitelist.
- Joint `coqchk -norec` of the seven new safe modules passes. This checks
  their module bodies while trusting dependencies; it is not a whole-library
  recursive kernel audit. The direct PTree client is separately recorded
  with its unsafe-hierarchy flag, not included in this safe kernel check.
- CI was neither inspected nor used as an acceptance condition.
