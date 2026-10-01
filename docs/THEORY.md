# Generic reasoning and its assumptions

The architecture is: backend probability laws, then one generic PTree proof.
Generic does not mean assumption-free or constructive. Concrete instances may
inherit classical/extensional axioms even when a generic proof is closed under
its explicit context. [Compiled contracts](../tools/data/CONTRACT_SUITES.json)
record actual types and logical dependencies; the profiles below are sufficient
requirements, not mathematical-minimality claims.

## Relations and stable observations

`pstruct` is structural equivalence, `pstrong` adds native relational sampling,
and `peutt` compares complete stable frontiers, including whole continuations
under matching visible events. Their client notations are `≡ₚ`, `≃ₚ`, `≈ₚ`,
with `[RR]` variants for heterogeneous return relations. Canonical `≈ₚ` fixes
the complete operation profile; raw `PEutt.peutt` permits explicit selection.
See [architecture](ARCHITECTURE.md) and [notation examples](CASE_STUDIES.md).

Stable hitting accumulates the mass reaching a Ret or Vis after internal
Tau/Prob computation. It does not normalize missing mass or make internal
sampling observable. `t ⇓ₕ front`, `t ⇓ₕ¹ front`, and `hit[n] t` expose the
complete, total-mass and finite judgments. Total stable mass is not necessarily
return termination: Vis is also a stable head. A finite certificate `t ⊢F front`
belongs to a different layer. Exact hitting records actual visible continuations;
behavioral replacement of them is a relational theorem, not tree equality.

## Bind and rewriting

[`Eq/Bind`](../theories/Eq/Bind.v) owns heterogeneous bind congruence:

```text
peutt RR t u
and forall x y, RR x y -> peutt RS (k x) (l y)
------------------------------------------------
peutt RS (bind t k) (bind u l)
```

It derives cofinality through `Eq/BindScheduling`, using probability-level
bind-order compatibility, directed cofinality and omega selection, alongside
the existing Core/Bind/order/omega/cofinality/diagonal and mixed laws.
It does not ask callers for a backend-specific PTree bind theorem.
`PEutt.peutt_bind_cofinal` retains an explicit scheduling premise for weaker
profiles. Since `RR` occurs only in premises, use `eapply peutt_bind` or
specify `RR`; there is no relation-guessing hint.

Do not assume `sem_eq -> sem_le` for the FreeOmega observable instance.
Quotient equality can identify a limit with another representation without
structural approximation in that direction. Finite scheduling instead uses
the separate approximation-order laws, and continuity identifies the limits.

[`Eq/Algebra`](../theories/Eq/Algebra.v) owns bind/fmap Proper theorems and
program equations. Shallow left-unit, Tau/Vis/Prob and fmap equations need
only frontier Core laws beyond their operations. Sampling fusion and mapping
use the relevant mixed/bind/omega laws; they do not require mass one or
commutativity. Right-unit and associativity currently use the structural
bridge below; that is a proof profile, not a proof that no weaker one exists.

Continuation congruences are pointwise. `peutt_visF_Proper` and
`peutt_probF_Proper` support rewriting through constructor expansions without
converting a continuation relation to Coq function equality. For completion
clients, opt into proof-backed registrations with:

```coq
From PTree.Interp.FreeOmega Require Import Rewriting.
Import FreeOmegaRewriting.
```

These exported, locally activated instances fix the observable interpretation;
they neither duplicate generic proofs nor create global search hints.

## Structural bridges and relational limits

[`Eq/Relation`](../theories/Eq/Relation.v) proves `peutt_of_pstruct` and
`peutt_of_pstrong`. Corresponding finite approximants can be related, but
ordinary bind continuity does not by itself relate their complete limits.
The additional probability property is:

```text
c and d increasing; lub c mu; lub d nu
forall n, lift R (c n) (d n)
------------------------------------
lift R mu nu
```

The bridge consumes explicit relational bind/mixed-bind/zero/lub certificates
with the ordinary native/frontier algebra and omega laws. They state measure
properties, not the desired PTree conclusion. FreeOmega supplies them through
its quotient construction. Unrestricted native MathComp relational-lub remains
an explicit premise; gluing alone does not discharge it.

Two independent positive results and a counterexample delimit this boundary:

- `Common/CountableRelationalLimit.oval_coupled_lub`: countably supported
  OmegaVal chains have a limiting joint for any Prop-valued relation.
  Bounded-test inequalities pass to the limit; countable transport realizes
  them. No injective enumeration, total mass or finite support is needed.
- `Interface/RelationalLimit.sem_lift_lub_of_joint_chain`: an explicitly
  increasing sequence of joints suffices under the ordinary bind/omega/AE laws.
  This does not construct such a sequence.
- Increasing marginals with a joint at every stage need not admit an
  increasing choice of joints. The finite `no_increasing_joint_selection`
  counterexample refutes that selection argument, not existence of a joint
  at the limit.

External OmegaVal results validate models; they are not imports or hidden
premises of generic behavioral reasoning. `coupling_ae_implies_ae_lift` is an
explicit derived probability constructor, not another global instance route.

## Coinduction up to contexts

| Rule | Closure allowed before the next progress obligation | Owner |
| --- | --- | --- |
| `peutt_coinduction_upto` | Previously established `peutt` | `Eq/PEutt` |
| `peutt_coinduction_upto_bind` | Related prefixes and candidate/known continuations | `Eq/PEutt` |
| `peutt_coinduction_upto_bind_vis` | Bind with one matching visible context | `Eq/UpToBind` |
| `peutt_coinduction_upto_prob` | Native relational sample and candidate/known continuations | `Eq/UpToProb` |

The bind/Vis rule derives scheduling using the generic bind profile; the
lower-level bind rule accepts explicit cofinality. The Prob rule uses native
Core, frontier Core/Bind/order/omega/cofinality/selection and mixed laws,
without requiring diagonal continuity, totality or commutativity.
Introduction lemmas such as `bind_upto_closure_bind`,
`prob_upto_closure_sample` and `vis_upto_closure_vis` expose the certificates
without asking clients to construct the closures' existential encoding.

All these rules allow heterogeneous return relations. They do not provide
unrestricted arbitrary-context closure. **Prob and Tau are not coinductive
guards**: the premise is complete stable-hitting progress. MixedHead uses a
proved relation on multi-node samplers inside up-to-bind/Vis; the interactive
VN service reuses sampler equivalence between visible request/reply boundaries.

## Model obligations at a glance

| Consumer | Additional boundary of the current proof |
| --- | --- |
| Generic bind / Proper | Bind-order, directed cofinality, selection; no supplied schedule |
| Structural-to-behavioral bridge | Relational limit closure and relational mixed laws |
| Full eventful iteration / arbitrary handler preservation | Relational zero/lub plus the scheduling/continuity profile |
| Guarded interpretation | AE-visible guard and its weaker probability profile |
| Complete-frontier iteration adequacy | Order/continuity scheduling; not relational-lub |
| MDP correspondence | Native/frontier reflection and fragment laws; not unrestricted relational-lub |

See [iteration](ITERATION.md), [interpreters](INTERPRETERS.md),
[MDP](MDP.md), and [backends](BACKENDS.md) for precise scope. Optional
commutativity is not a default requirement. No universal backend symmetry is
claimed merely because the upper-layer theorem is generic.
