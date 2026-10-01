# Loops, complete frontiers and least fixed points

There are two different tasks: relating loop programs, and calculating the
complete frontier of one loop. Neither is a termination theorem by itself.
All owners below are generic unless explicitly identified as model validation.

## Behavioral iteration and full uniformity

[`Interp/IterationUniform`](../theories/Interp/IterationUniform.v) proves
`peutt_iter_direct_rel`, with heterogeneous loop states and return relations,
and packages the full `ptree_peutt_iteration_uniform` interface. Uniformity is:

```text
forall i, map (h + id) (f i) ≈ g (h i)
-----------------------------------
forall i, iter f i ≈ iter g (h i)
```

No injectivity of `h`, AST, no-event condition or supplied generator closure
is needed. The direct restart machine keeps the active PTree as state:
`Ret (inl i)` restarts, `Ret (inr a)` exits, Tau/Prob advance internally, and
Vis exposes the actual recursive continuation. Finite approximants match the
program's primitive hitting approximants in both order directions. The bounds
`grid n m <= primitive ((n+1)*(m+1))` and `primitive n <= grid n n`, followed
by directed cofinality/diagonal/Fubini, justify the complete machine semantics.

The relational theorem requires frontier Core/Bind/order/omega, cofinality,
diagonal/Fubini, bind/mixed-bind order, directed cofinality, selection, and
`relational_zero` / `relational_lub`. Full uniformity additionally consumes the
native/structural return-map bridge. The FreeOmega specialization supplies the
existing completion certificates; MathComp keeps gluing and relational-lub
explicit in Gate M. Refer to the compiled contracts for logical dependencies.

This direct proof avoids the old synthetic-event proof's restriction that a
loop state fit an event-response universe. The old packaging failure remains
a cause-sensitive negative test; the new full package is checked after safe
AllImports, including a whole PTree as loop state. It supports actual PTree
targets for the State/Exception fold squares. It does not make every syntax
and interface universally universe-polymorphic.

`Eq/Iter` also retains the weaker-profile generator-closure rule;
`Interp/IterationAlgebra` supplies structural unfold/naturality/codiagonal
and behavioral laws under their stated profiles. Those routes remain useful;
do not confuse their premises with the full direct theorem or assert every
Conway/Elgot law for an arbitrary MonadIter.

## Complete-frontier iteration

[`Interp/FrontierIteration`](../theories/Interp/FrontierIteration.v) accepts:

```text
step  : I -> ptree E MN (I + A)
front : I -> MF (stable_head E MN (I + A))
forall i, step i ⇓ₕ front i
```

One complete head is resolved as follows:

| Head | Meaning |
| --- | --- |
| `FHRet (inl j)` | Retry at `j` |
| `FHRet (inr a)` | Absorb at `FHRet a` |
| `FHVis e k` | Absorb at Vis, retaining the actual iterated continuation |

The whole frontier is bound through this kernel: no single head is selected
and no mass is normalized. `iteration_summary_round` iterates complete rounds;
round zero already retains Ret/Vis exits, while unresolved retries give zero.

- `iteration_summary_hitting`: complete step certificates and a summary lub
  give an actual hitting witness for `iter step i`.
- `iteration_summary_exists`: produces a summary/hitting witness.
- `iteration_summary_hitting_eq`: compares a summary with any actual witness.
- `iteration_summary_round_unfold`: exposes the round recurrence under `sem_eq`.

Clients need no separate cofinality argument, finite stopping bound, `no_event`,
total mass, finite state space or finite native limit. `MF` is arbitrary; the
step itself may have unbounded internal computation. Adequacy uses the existing
order/continuity scheduling laws, not Core/coupling, relational-lub or native
measure laws. The optional algebraic unfolding has its own Core/Bind premises.

Exact certificates must mention the actual visible continuations. Replacing
them by behaviorally equivalent programs requires whole-head lifting, not a
silent substitution in the hitting predicate. The older native-round and
staged absorbing-exit conveniences remain special-purpose APIs, not competing
semantics. VN and Adaptive may analyze only a bit observation and retain the
full frontier abstract; RandomWalk's infinite-support result need not fit MN.

## Return-only frontiers and classical iteration

[`Prob/Interface/KleisliIteration`](../theories/Prob/Interface/KleisliIteration.v)
defines, for `K : I -> MF (I + A)`:

```text
Phi X i = bind (K i) [inl j => X j | inr a => ret a]
approx 0 i = zero
approx (S n) i = Phi (approx n) i
sem_iter K i out = sem_lub (approx · i) out
```

[`Interp/ReturnIteration`](../theories/Interp/ReturnIteration.v) proves:

- `iteration_summary_round_return_only`: round `n` equals the FHRet image
  of classical approximant `S n` under `sem_eq`.
- `iteration_summary_return_only`: summary and classical limit witnesses agree.
- `iteration_summary_mixed_iter`: compatibility with the existing native kernel
  `mixed_iter`.
- `ptree_iter_return_only` / `ptree_iter_mixed_iter`: complete certificates for
  actual steps yield an actual loop hitting witness and that equality.

The condition is local to the step frontier, not that the entire signature is
empty. Zero-prefix cofinality removes the finite index shift at the limit.
Since generic `sem_lub` is not assumed saturated in its output under `sem_eq`,
the theorem constructs a hitting witness and proves equality; it does not
silently replace a predicate witness by any equal measure.

## Fixed point versus least fixed point

`sem_iter_fixed_point` proves the unfolding equation under `sem_eq`. For endless
retry, a nonzero Dirac can also satisfy the fixed-point equation, so this alone
is not leastness. `sem_iter_least_fixed_point` additionally consumes explicit
upper-bound and least-upper-bound properties of `sem_lub`.

These properties are not silently asserted for raw FreeOmega approximation.
Two mathematical models provide genuine leastness:

- Safe `Prob/Backend/MathComp/Iteration` constructs native measure iteration and
  proves leastness without gluing; recursive PTree assembly remains Gate M.
- Independent `Prob/Domain/Iteration` proves `oval_iter_fixed_point` and
  `oval_iter_least_prefixed`. `FreeOmega/Validation/Iteration` proves that the
  canonical formal iteration denotes this lfp and is modelable. Other
  quotient-equal witnesses require the quotient-validation obligations.

Start with [IterationBasics and AbsorbingFrontier](CASE_STUDIES.md) for actual
program proofs. Contracts are in the generic-algebra and iteration groups;
[verification](AUDITING.md) explains how to check them without conflating safe
proofs, Gate M clients, or historical validation runs.
