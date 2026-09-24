# Behavioral handler calculus

Baseline: `a8275df` (the extraction/factory work is unchanged).

## Result

Handlers over a fixed native probability carrier are pure functions:

```coq
Handler MN E F := forall X, E X -> ptree F MN X.
```

`Core/Handler.v` defines `id_`, `cat`, `case_`, `inl_`, `inr_`,
`bimap` and `empty`, without importing probability laws or equational theory.
Composition is forward: `cat h g e = interp g (h e)`. It changes effects,
not the native probability representation.

`Interp/HandlerRelation.v` defines `peutt_handler` as pointwise
`peutt eq`, and proves:

```text
(forall X (e : E X), peutt eq (h1 X e) (h2 X e))
  + peutt RR t u
  -------------------------------------------------
  peutt RR (interp h1 t) (interp h2 u)
```

Both result carriers and their relation may differ. There is no structural
equality, guarding, totality, termination, or target-preservation premise on
the handlers. They may return internally or execute unbounded internal work.
This is about whole-continuation `peutt`, not `tree_trans_bisim`.

The original fixed-handler `Unrestricted.peutt_interp` now specializes this
theorem. Its compiled signature and logical assumptions are unchanged.
The guarded route remains separately maintained, with its more local
AE-visible sufficient condition and different probability assumptions.

## One generic proof, no new capability

`RelationalPreservation.v` owns the two-handler complete-frontier fusion
criterion and up-to-bind preservation proof. The old
`Preservation.peutt_interp_of_vis_fusion` specializes both handlers to one;
its old definition, criterion, public signature and remaining proofs stay
unchanged.

The relational machine proof uses the existing physical/accelerated machines:

- source configurations carry the given source `peutt RR`;
- active handler configurations carry `peutt eq active1 active2` and
  pointwise related source continuations;
- complete-frontier coupling comes directly from
  `peutt_state_hitting_lift`;
- a handler return becomes an internal source transition;
- only a target visible head uses the bind-compatible candidate;
- `stable_hitting_rel` lifts the two different kernels to their limits;
- existing `handler_machine_hitting_sound` is applied independently on
  both sides.

No recursive target equivalence is assumed before a visible guard. No
handler-law class, existence axiom, global hint or route registration is added.
The original machine implementation and its acceleration proofs are frozen.

The generic replacement theorem consumes the same probability profile as
the fixed-handler theorem: frontier Core/Bind; MixedMeasure operations;
order/omega; constant/prefix and directed cofinality; bind/mixed-bind order;
diagonal/Fubini; omega selection; and explicit `relational_zero` /
`relational_lub`. It does **not** require a native `SemanticMeasure`
or a native relational mixed-bind law merely to replace handlers.

## Handler algebra

`Interp/HandlerFacts.v` supplies:

| Endpoint | Meaning |
| --- | --- |
| `peutt_interp_identity` | interpreting with trigger preserves the tree behavior |
| `peutt_interp_trigger_event` | interpreting one trigger gives its handler behavior |
| `handler_cat_congr`, `handler_cat_Proper` | composition respects pointwise behavioral equivalence |
| `handler_cat_id_l/r`, `handler_cat_assoc` | category unit and associativity laws |
| `handler_case_congr`, `handler_case_inl/inr` | case congruence and injection equations |
| `handler_case_eta`, `handler_case_eta_cat`, `handler_case_cat` | case reconstruction and post-composition |
| `handler_bimap_congr` | both branches may be replaced behaviorally |
| `handler_empty_unique` | empty signature's handler is unique modulo the relation |

The laws are modulo `peutt_handler`, not equality of Coq functions.
`peutt_handler_equivalence` is an explicit constructor, not a new global
typeclass search rule.

Assumptions are retained only when used (see compiled signatures):

- case congruence/eta, case post-composition and empty uniqueness use the
  basic behavioral relation;
- composition congruence uses the full unrestricted probability profile;
- the trigger equation, left unit, associativity and case injection equations
  use the existing generic structural-to-behavioral bridge, including native
  Core and `relational_mixed_bind`;
- identity interpretation and the right unit use generic hitting/order
  continuity, **without** relational-lub, Fubini or a native measure instance.

That last proof does not silently assume a missing arbitrary-frontier right
unit law. `handler_finite_front_ret` derives right unit up to approximation
order for native-generated finite hitting approximants. Bind continuity and
directed cofinality then give `handler_complete_front_ret` for complete
hitting witnesses. A direct stable-head coinduction proves interpreter
identity. No foundation or backend law is strengthened.

## Model specializations and public use

`Interp/FreeOmega/HandlerCompletion.v` only discharges probability-level
obligations using existing generic completion instances. Its names start with
`free_omega_`; they do not shadow generic theorem names through export order.
There is no SubEnumQ-specific or SubEnumR-specific handler proof.

```coq
From PTree Require Import PTree PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ.

(* Hh : forall X e, h1 X e ≈ₚ h2 X e
   Ht : t ≈ₚ[RR] u *)
eapply free_omega_peutt_interp_handler_rel; [exact Hh | exact Ht].
```

`PTree.v` still exports only Core construction modules.
`PTreeFacts.v` now exports the generic handler owners and the unique-named
completion endpoints, as well as the already-proved State, Reader, Writer
and Exception definitions/facts. The generic `peutt_interp` and
`run_state_peutt` keep their explicit model obligations. No concrete backend,
external validation, internal certificate machinery or Gate M module is
loaded through these entry points.

There are explicit fixed-result and polymorphic `Proper` lemmas. The latter
uses `forall_relation` because `interp` places its result carrier after its
handler argument; this is what lets actual `setoid_rewrite Hh` rewrite the
handler in the existing API. Clients register a concrete instance locally;
nothing asks global search to invent handler equivalence.

`PublicHandlers.v` is a public-only rational client. It checks:

- immediate-return versus Tau-prefixed handler, with a proof that these are
  **not** structurally related;
- heterogeneous result carriers and relations;
- infinitely many eliminated source events;
- a real handler-argument `setoid_rewrite`;
- units, associativity, case injection and bimap congruence;
- a signature carrying types strictly above Set.

`HandlerCalculus.v` uses arbitrary `SubEnumR R bool` weights, target visible
events and a coinductive source service. It obtains handler replacement and
a subsequent bind equation through the same completion/generic theorems.
This is not a new irrationality or termination theorem.

MathComp Gate M is unchanged. Instantiating arbitrary-handler replacement
there still needs the unresolved general relational-lub obligation; native
bind/omega mathematics alone is not asserted to supply it.

## Preservation and checks

`audit_handler_calculus.py` starts from all 369 old theory modules. It permits
only seven new modules, exact proof delegation in two old owners, specified
public exports/boundary checks, and sorted AllImports additions. Every other
old theory source remains byte-for-byte unchanged, including canonical
routing, probability classes, qlift, execution and MathComp Gate M.

Before historical audits run, a checked adapter reconstructs the exact old
snapshot; it rejects unauthorized changes rather than broadening old gates.
Existing compiled snapshots are not regenerated. The new snapshot contains
60 elaborated types and per-endpoint logical assumptions. The old 27-endpoint
machine audit and 11 original fusion/guarded contracts also run unchanged.

The two-handler fusion/machine/preservation proofs are closed under their
explicit context. Handler equivalence and some elementary equations inherit
the existing `eq_rect_eq` dependency from behavioral transitivity/structural
reasoning. FreeOmega specializations inherit the existing functional
extensionality and `eq_rect_eq`. These are recorded per endpoint, not hidden
as probability capabilities; the logical-axiom whitelist is unchanged.

The public surface policy is updated explicitly. The source-contract registry
also registers the existing finite-runner regression, which already had its
dedicated stage audit but was absent from the all-regression registry.

## Remaining boundary

Generic arbitrary-target `fold` algebra is deliberately deferred. A bare
`MonadIter` does not imply lawful iteration, sampling-respecting
interpretation or `peutt` preservation. StateT/fold uniformity and existing
execution results are unchanged.

This increment does not introduce arbitrary-backend realization, alter
transition bisimulation, extend MathComp's checker bypass, change extraction,
or revisit CI.

## Local verification

Completed for this increment:

- Full `opam exec -- dune build`, including safe AllImports and existing
  extraction targets.
- All 277 Python tool tests.
- Architecture, aggregate coverage/order, public surface and soundness source
  audits: 376 modules, of which 374 are Gate S and the same two are Gate M.
- All 465 old mainline compiled contracts unchanged; all 27 original machine,
  11 fusion/guarded, 31 standard-effect and 28 State contracts unchanged.
- All 60 new compiled contracts checked, with per-endpoint assumptions.
- Joint `coqchk -norec` of nine safe module bodies: Core.Handler,
  Interp.RelationalPreservation, HandlerRelation, HandlerFacts, Preservation,
  Unrestricted, FreeOmega.HandlerCompletion, and the two new regressions.
- `git diff --check`.

The kernel check trusts compiled dependencies; it is neither a recursive
whole-library audit nor a universe-safe claim about Gate M. No CI run was
queried, requested or used as evidence. The build emitted only the existing
extraction opacity/output-directory warnings, not an extraction change.
