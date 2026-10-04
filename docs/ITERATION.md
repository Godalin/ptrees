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
- `ptree_iter_return_only_equiv`: the actual complete step witness need only
  be `sem_eq` to the return image of the kernel. This avoids assuming generic
  output saturation and supports compositional language denotations.

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
FreeOmega now has a separate internal preorder (below); two independent
mathematical models also provide genuine leastness:

- Safe `Prob/Backend/MathComp/Iteration` constructs native measure iteration and
  proves leastness without gluing; recursive PTree assembly remains Gate M.
- Independent `Prob/Domain/Iteration` proves `oval_iter_fixed_point` and
  `oval_iter_least_prefixed`. `FreeOmega/Validation/Iteration` proves that the
  canonical formal iteration denotes this lfp and is modelable. Other
  quotient-equal witnesses require the quotient-validation obligations.

### Public FreeOmega semantic order

Import `Prob/FreeOmega/Definition` and `Prob/FreeOmega/IterationOrder` (the latter
exports `DomainOrder`), then opt in with `Import FreeOmegaOrderNotations` and
`Local Open Scope freeomega_scope`.
`t ⊑ω u` is `free_omega_sem_le t u`. The existing `sem_le = free_omega_approx eq`
and `sem_eq = free_omega_qlift eq` are unchanged.

The new preorder is the least **rule-generated relation on the existing
carrier**, not another free completion or an interpretation into OmegaVal.
Its rules include structural approximation, observable equality, transitivity,
sample/raw-Lub congruence, and upper/least rules for **structurally increasing**
chains. The supremum rules are part of this relation's definition; their
independent mathematical soundness is proved in `Validation/DomainOrder`.
Bind monotonicity on both sides is derived, not an additional rule or axiom.

Public proof rules:

- `free_omega_approx_sem_le`, `free_omega_sem_eq_le`: old proofs embed.
- `free_omega_sem_eq_le_proper`: quotient rewriting inside inequalities.
- `free_omega_lub_upper` / `free_omega_lub_least`: literal `FOLub` supremum.
- `free_omega_sem_lub_upper` / `free_omega_sem_lub_least`: any existing lub witness.
- `free_omega_bind_sem_mono`: monotonicity in source and continuation.
- `free_omega_iter_least_prefixed`: `Phi Y ⊑ω Y` bounds the canonical iteration.
- `free_omega_iter_least_fixed_point`: existing qlift fixed-point equation
  **and** new-preorder leastness. `free_omega_sem_iter_least_prefixed` works
  with any selected/quotient-equivalent iteration witness.

Leastness needs native Core laws, not native omega-completeness or a model.
The qlift fixed-point equation additionally uses the existing native coupling-AE
and countable-AE profile. A pre-fixed bound may be any raw term.

This is deliberately not an arbitrary-chain omega-CPO theorem. We do not claim
antisymmetry up to qlift, completeness for evaluator order, or validity of raw
terms. Modelability remains separate: structural increasingness alone does not
make an invalid constant chain valid. With modelable terms, existing validation
supplies the genuine OmegaVal limit; the new preorder soundly implies its order.
`Validation/Iteration.free_omega_iter_denotes_lfp` identifies the public
iteration with `oval_iter` by directly reusing that earlier validation proof.

`Examples/PGCL/FreeOmega.pgcl_while_least_fixed_point` applies this public tool
to the ordinary functional `Phi Y s = if b s then bind (D c s) Y else ret s`.
Unlike generic `denote_while_least`, it needs no supplied supremum laws.
`RandomWalk.walk_denote_least_fixed_point` instantiates it for the forward
random-walk functional, with its infinite-support result still in FreeOmega.
No external validation module enters these program proofs.

## pGCL forward semantics (no wp or external model)

[`Examples/PGCL`](../theories/Examples/PGCL) implements the purely probabilistic
fragment: skip, divergence, state update, sequencing, conditionals, probabilistic
choice and unbounded while. State expressions are shallow functions; commands
are an inductive syntax. There is no demonic choice or conditioning. Parameters
of probabilistic choices are abstract; the finite instances supply bounded
rational/real Bernoulli coins, including probabilities zero and one.

The proof chain is:

```text
command
  -> elaborate : PTree (stateE S + E) MN unit
  -> run       : PTree E MN S       (public interp_state, then state projection)
       ≈ execute                    (explicit-state normal form)
       -> complete hitting frontier = map FHRet (denote command state)
```

`Forward.v` independently defines `denotes coin command K`, where `K : S -> MF S`.
It uses only the abstract probability interfaces. Sequential composition is
Kleisli composition; `forward K mu := sem_bind mu K` transports an initial
distribution. While is **bottom-started** `sem_iter (while_kernel b K)`, not
an arbitrary solution of its unfolding equation. An existing omega-selection
capability supplies a convenient `denote` function; existence and uniqueness
up to `sem_eq` are proved. The relational specification itself needs no selection.

Opt in to `PGCLNotations` / `pgcl_scope` and `PGCLDenotationNotations` /
`pgcl_denotation_scope`:

```coq
UPDATE f ;; WHILE b DO (c ⊕[ p ] d) OD
IF b THEN c ELSE d ENDIF
x ::= e
⟦ c ⟧[ coin ] s          (* selected forward kernel *)
c ⇓[ coin ] K            (* relational forward denotation *)
c ≈g[ coin ] d          (* equal forward kernels; PGCLAlgebraNotations *)
```

The explicit coin argument avoids another canonical-backend selection mechanism.
`ENDIF` deliberately does not reserve the common interface name `FI`.

Main endpoints and their boundaries:

- `Adequacy.pgcl_forward_correspondence`: arbitrary `MN/MF`, any complete
  hitting witness of `execute`, whole-frontier equality with the forward kernel.
  `returns_iter` uses the existing return-only iteration bridge, including its
  finite `n` versus `S n` shift. No bounded-body, AST, native finite-limit or
  empty-event-signature assumption is needed.
- `StateInterpretation.run_execute`: generic behavioral State elimination,
  using existing relational mixed-bind/zero/lub certificates and uniform iteration.
- `FreeOmega.pgcl_run_denotes_iff`: for any native backend satisfying the
  maintained FreeOmega profile, relational forward denotation iff its return
  image is an actual complete frontier of `run`. Exact witness replacement
  here uses FreeOmega's existing saturated limit predicate; it is not asserted
  for an arbitrary abstract `sem_lub`.
- `Finite.rational_pgcl_hitting` / `real_pgcl_hitting`: SubEnumQ/SubEnumR
  specializations of that same theorem. No new completion or coupling proof.
- `Forward.denote_while_unfold` / `denote_while_approximants`: classical
  Kleisli equations. `denote_while_least` additionally exposes genuine lub
  upper/least properties, just like `sem_iter_least_fixed_point`; those
  properties are **not** silently assumed of raw FreeOmega.

`Algebra.v` is the backend-parametric source equational library. `cequiv` is
pointwise `sem_eq`, not syntax equality or functional extensionality. Sequence,
conditionals, probabilistic choice and while have `Proper` instances, so source
equations rewrite below program contexts. Laws include skip/assignment equations,
sequence associativity, postcomposition distribution over conditionals/choices,
while unfolding and endless skip. The minimal `BindLaws` does not include right
unit: `seq_skip_r` exposes that ordinary measure law; `FreeOmega.pgcl_seq_skip_r`
discharges it from the existing completion proof. `pgcl_run_Proper` transports
source rewrites into behavioral State-interpreted programs.
The abstract coin need not have mass one, so the library does not silently
assume choice idempotence for arbitrary subprobabilistic samplers. Concrete
rational/real Bernoulli clients use normalized coins.

`Programs.v` demonstrates source rewrites, retry, nested loops, partial termination
and zero frontier for endless skip. The public random-walk entry is now
`PGCL/RandomWalk.v`: `walk_source` is pGCL syntax and `walk_denote_closed_form`
starts with its **forward denotation**. It represents this denotation by the
`S n` Kleisli approximants, observes their exact finite native distributions,
and reuses the normalized geometric atom limits. `RandomWalkAnalysis.v` contains
the preserved passage/harmonic analysis. No second convergence proof or finite
native representation of the infinite-support limit is introduced. `walk_run`
and `walk_classical_frontier` retain the connection with the analysed PTree.
The old import `PTree.Examples.RandomWalk` moves to
`PTree.Examples.PGCL.RandomWalkAnalysis`; no compatibility facade is retained.

All these modules are Gate S and import no external validation model. The generic
forward correspondence and conditional leastness theorem are closed under their
explicit contexts. State/behavioral assembly inherits existing dependent equality
and relational/unique choice dependencies; completion and finite instances also
inherit existing extensionality/MathComp choice. Compiled contracts record these
per endpoint, without broadening the external-soundness whitelist.

Start with [IterationBasics and AbsorbingFrontier](CASE_STUDIES.md) for actual
program proofs. Contracts are in the generic-algebra and iteration groups;
[verification](AUDITING.md) explains how to check them without conflating safe
proofs, Gate M clients, or historical validation runs.
