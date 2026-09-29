# Public modules and relation ownership

## Entry points

```coq
From PTree Require Import PTree.       (* construct programs *)
From PTree Require Import Eq.          (* relations and their notation *)
From PTree Require Import PTreeFacts.  (* equational/interpreter facts *)
From PTree.Eq.Backend Require Import SubEnumQ. (* choose a native profile *)
```

`PTree` exports syntax and combinators. `Eq` exports the relation owners and
canonical selection. `PTreeFacts` exports actual generic Eq and Interp theorem
owners, together with FreeOmega completion-specific results. It does not
choose a concrete backend. `Semantics` is the independent transition/MDP
comparison entry point.

There is no `theories/API/` layer or alias facade. Backend route modules
export their native representation, with probability definitions and laws
owned by Prob. For example, `Eq/Backend/SubEnumQ` does not import Interp;
concrete interpreter endpoints have their own `Interp/Backend/SubEnumQ` owner.

## Relations and canonical selection

| Owner | Notation module | Relation |
| --- | --- | --- |
| `Eq/PStruct` | `PStructNotations` | `≡ₚ`, `≡ₚ[RR]` → `pstruct` |
| `Eq/PStrong` | `PStrongNotations` | `≃ₚ`, `≃ₚ[RR]` → `pstrong` |
| `Eq/Canonical` | `PEuttNotations` | `≈ₚ`, `≈ₚ[RR]` → `canonical_peutt` |

Raw `PEutt.peutt` remains parameterized by arbitrary native/frontier models.
Canonical selection fixes the frontier **and its operations**, including
equality/lifting, mixed bind and omega structure. It bundles no law and adds
no blanket route for an arbitrary native carrier. The finite-backend routes
choose observable FreeOmega, not its auxiliary structural interpretation.
See [canonical routing](CANONICAL_BEHAVIOR_ROUTING.md).

## Heterogeneous bind

`Eq/Bind.peutt_bind` is the single public generic theorem. Given arbitrary
`RR : R1 -> R2 -> Prop` and `RS : A -> B -> Prop`, it proves:

```text
peutt RR t1 t2
+ (forall x y, RR x y -> peutt RS (k1 x) (k2 y))
    -> peutt RS (bind t1 k1) (bind t2 k2)
```

Continuations need behavioral relatedness, not Coq function equality. The
theorem consumes explicit probability-level algebra/order/limit laws;
backends instantiate those laws, not separate copies of bind congruence.
`Eq/PEutt.peutt_bind_cofinal` retains the lower-level explicit cofinality
premise. [Generic bind](GENERIC_BIND.md) records the exact distinction.

The minimal public client uses `PTree PTreeFacts` and the chosen backend:
`eapply peutt_bind; eassumption`, or
`apply (peutt_bind (RR := RR)); assumption`. Since `RR` appears only in
premises, naked `apply` need not infer it. No guessing hint or export-order
shadowing is used to select the theorem.

## Dependency and verification boundaries

Direct owner exports expose helpers as well as selected endpoints; there is
no facade-based promise to hide every implementation short name. The tested
boundaries are semantic dependencies:

- `PTree` alone loads no local probability interface or relation theory.
- `Eq` does not load FreeOmega bind or interpreter theory.
- `PTreeFacts` loads no concrete carrier, `Eq/Internal` or external Domain.
- Safe entries do not load the universe-unchecked MathComp route.

Minimal-import, canonical import-order and local structural-registration
clients remain separately compiled tests. The safe aggregate and exact Gate M
allowlist are independent checks; a successful full build is not a claim that
Gate M was universe-checked. See [AUDITING](AUDITING.md) for current commands
and kernel-check scope, and [MathComp](MATHCOMP.md) for its trust boundary.

The former facade/migration reports are archived in Git. This document describes
current ownership, not the historical `API/Generic` / `API/FreeOmega` export
order or their retired replay tools.
