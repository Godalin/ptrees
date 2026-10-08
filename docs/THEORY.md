# Generic reasoning and its assumptions

The architecture is: backend probability laws, then one generic PTree proof.
Generic does not mean assumption-free or constructive. Concrete instances may
inherit classical/extensional axioms even when a generic proof is closed under
its explicit context. [Compiled contracts](../tools/data/CONTRACT_SUITES.json)
record actual types and logical dependencies; the profiles below are sufficient
requirements, not mathematical-minimality claims.
The [assumption guide](AUDITING.md#logical-assumptions-and-their-roles) separates
dependent inversion, extensionality, witness choice and concrete backend
mathematics; being UIP-free is not the same as being assumption-free.

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

Read the stable-behavior construction in this order (names relative to
`PTree.Eq`):

1. [`UnifiedFrontier.stable_head`, `stable_head_rel`](../theories/Eq/UnifiedFrontier.v)
   expose Ret values and whole Vis continuations as the observations to relate.
2. [`PTreeKernel.ptree_hitting_increasing`, `ptree_stable_hitting_exists`,
   `ptree_stable_hitting_unique`](../theories/Eq/PTreeKernel.v) construct and
   identify the complete frontier using the stated order/omega laws.
3. [`StableHittingRelation.stable_hitting_match`](../theories/Eq/StableHittingRelation.v)
   matches complete witnesses in both directions. [`PEutt.peutt`,
   `peutt_coinduction`](../theories/Eq/PEutt.v) use that matching as their
   generator; progress is at stable observations, not at a single internal
   sampling node.
4. [Relational-limit laws](#structural-bridges-and-relational-limits) connect
   approximation-level relations to complete frontiers. They are additional
   probability obligations, not consequences of the datatype alone.

The bind, up-to and interpretation interfaces below consume this structure;
their clients need not reopen its scheduling or dependent-view proofs.

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
| `peutt_coinduction_upto_peutt` | Candidate surrounded by known homogeneous `peutt eq` | `Eq/UpToPeutt` |
| `peutt_coinduction_upto_peutt_known` | The preceding closure or an already proved heterogeneous pair | `Eq/UpToPeutt` |
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

The up-to-peutt rule is a **coinduction principle**, not just congruence of
the final equivalence. With `W_A = peutt eq` on the left carrier and `W_B`
on the right, its closure is `C(X) = W_A ; X ; W_B`. It proves
`X ⊆ peuttF(C(X)) → X ⊆ peutt RR`. The return relation `RR` is arbitrary;
only the surrounding, already established equivalences are homogeneous.
The proof composes generator-level hitting matches and frontier liftings,
establishing `C(peuttF(X)) ⊆ peuttF(C(X))`. It needs frontier Core laws but
no Bind laws, Omega laws, cofinality, hitting-existence or backend-specific
validation premises; MixedMeasure and SemanticOmega supply operations.
Both up-to-peutt rules are closed under the global context, apart from the
semantic profile explicitly quantified in their signatures. Stable-head
composition uses a dependent view retaining the response type, event and
continuation together, rather than UIP-based dependent inversion. The same
cleanup removes `Eqdep.Eq_rect_eq.eq_rect_eq` from `peutt_sym`, `peutt_trans`,
heterogeneous `peutt_rel_compose`, `peutt_bind_cofinal` and up-to-bind.
This is not an axiom-freedom claim for every backend or the whole library;
the compiled contracts continue to record remaining dependencies separately.

FreeOmega's shared structural laws now also avoid UIP: the AE, lifting and
approximation constructor views in `StructuralMeasure.v` preserve dependent
sample packages without identifying equality proofs. AE conjunction,
countable AE, lifting/approximation composition and AE transport/restriction
are closed under the global context, with their native laws explicit in the
signatures. Support transport and quotient-support proofs reuse these views;
the observable Core, countable-AE, CouplingAE, OmegaAE, Diagonal and Fubini
instances are now also closed under the global context, with native laws
explicit in their types. This does not remove assumptions from concrete
native instances. Observation uniqueness also uses a constructor view and
is closed under the global context. Structural and observable bind laws
still use functional extensionality, and structural coupling realization
retains its existing classical choice dependencies.

The `PStruct` transitivity, bind and iteration proofs and the `PStrong`
transitivity and bind proofs now avoid UIP, without changing their statements.
This also removes UIP from the generic interpreter's trigger law. The
fixed-carrier inversion lemmas `pstrong_vis_inv` and `pstrong_prob_inv`
still depend on `Eqdep.Eq_rect_eq.eq_rect_eq`: unlike the one-sided packaged
views, they recover continuations at a specified hidden type. Both remaining
dependencies are explicitly recorded in the contracts; no necessity or
impossibility theorem for eliminating them is claimed.

Structural interpreter preservation and handler replacement now also use
ordinary constructor elimination: all five `Interp/Structural.v` theorem
endpoints are closed under the global context. Head bisimulation symmetry,
transitivity, equivalence and step matching reuse the packaged stable-head
view/composition lemmas and are likewise closed, with their semantic profile
explicit. `head_step_vis_label` now keeps the response existential in a
one-sided constructor view and is also closed. Likewise,
`related_heads_enable_same_label` transports enabling through related heads
without fixing or inverting a response equality; it is closed even for an
arbitrary return relation, not just equality.

The stronger fixed-response/fixed-event inversions `head_step_vis_iff` and
`head_bisim_vis_iff` still use UIP; their uniqueness and
chosen/existential-hitting corollaries inherit it. The one-sided view only
gives `label = Obs e y` for some response `y`; at a specified `Obs e x`,
recovering the original `k x` requires an additional dependent-package
alignment, not ordinary constructor elimination. `peutt_head_action_results`
now uses the view for the first transition but still uses the fixed-response
inversion for the second. Thus `peutt_preserves_trans`, `peutt_trans_bisim`
and generic MDP transition coincidence retain their existing UIP dependency.
No definitions or theorem statements were changed, and no necessity or
impossibility result about eliminating this remaining dependency is claimed.

The finite-observation transport `ptree_hitting_observes_pstruct` reuses
`free_omega_observes_inv` and is closed under the global context. FreeOmega's
`iter_complete_rows_behavioral_lift` and
`peutt_iter_behavioral_rel_of_outputs` are likewise closed. The version that
selects complete outputs, `peutt_iter_behavioral_rel`, still uses relational
choice and dependent unique choice, but no UIP. Eliminating dependent
inversion does not eliminate the separate choice of semantic witnesses.

The maintained pGCL contracts, including State lowering, Q/R hitting,
`walk_run`, `walk_classical_frontier` and `compile_hitting`, no longer depend
on UIP. RandomWalk's `random_walk_ast`, `random_walk_outputs_spec` and
`random_walk_closed_form` retain functional extensionality but no UIP.
The rational upper evaluator's AE monotonicity/extensionality also reuse
the existing FreeOmega AE view; their remaining classical mathematics is
unchanged. These are per-endpoint dependency claims, not constructivity
claims about all probability backends.

Other audited paths still use UIP: ITree reflection, the separate FreeOmega
translation proof, finite-interaction query preservation and syntactic
probabilistic-tree validity under bind/iter. These are not the core `peutt`
equivalence/bind/iteration proofs. See the assumption guide for precise
examples; do not extend the core UIP-free claim to every interpreter,
observation, validity theorem or case study.

Pure `C` does not close an unrelated known pair: `C(empty) = empty`.
The `_known` variant uses `C(X) ∪ peutt RR` for that purpose. Closure Proper
instances let a client use `setoid_rewrite` before re-entering its candidate;
they do not assert that an arbitrary candidate itself respects `peutt`.
Neither rule licenses transitivity of unknown candidate pairs or arbitrary
composition with another up-to technique. MixedHead's existing proofs are
unchanged; applying this new rule there is a separate presentation task.

All these rules allow heterogeneous return relations. They do not provide
unrestricted arbitrary-context closure. **Prob and Tau are not coinductive
guards**: the premise is complete stable-hitting progress. MixedHead uses a
proved relation on multi-node samplers inside up-to-bind/Vis; the interactive
VN service reuses sampler equivalence between visible request/reply boundaries.

The alternative `Examples/MixedHead/UpTo` proof separates up-to-bind context
reasoning from ordinary coinduction with native coupling of complete frontiers.
It does not need the probability up-to closure: coupling handles the probability
layer, while Challenge/Reply supply visible progress. The probability closure
remains an available library rule, not a second technique required by this case.

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
