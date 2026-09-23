# Canonical behavioral routing — foundation gate

Baseline: `04475b2`. This implements proposal steps 1–4, not the subsequent
public-notation, bind-facade or example migration. No CI work is performed.

## Problem and boundary

The same raw `FreeOmega MN A` supports two relation interpretations:

| Interpretation | Equality/lifting | Role |
| --- | --- | --- |
| Structural | `free_omega_lift` | Internal constructor-sensitive proofs |
| Observable | `free_omega_qlift` | Canonical behavioral theory |

Selecting only the carrier does not determine `peutt`. Before this gate a
minimal PTree/SubEnumQ client could infer the correct FreeOmega carrier but
the structural operations; weighted EnumQ could infer a native self-frontier.
The remedy is explicit operation selection, not a change to either relation.

## Structural registration

All eleven original `StructuralMeasure` instances are enumerated from the
frozen source. Ten now use `#[local] Polymorphic Instance`:

- `FreeOmegaSemanticMeasure`
- `FreeOmegaSemanticMeasureCoreLaws`
- `FreeOmegaSemanticMeasureAEKleisliLaws`
- `FreeOmegaSemanticMeasureCountableAELaws`
- `FreeOmegaSemanticMeasureCouplingAELaws`
- `FreeOmegaSemanticMeasureBindLaws`
- `FreeOmegaMixedMeasureLaws`
- `FreeOmegaSemanticOmega`
- `FreeOmegaSemanticOmegaLaws`
- `FreeOmegaSemanticMeasureOrderLaws`

`FreeOmegaMixedMeasure` remains global: `mixed_bind := FOSample` is shared by
both interpretations. No constant, proof or class field was deleted/renamed.

`Eq/FreeOmega/{Base,Bind,Relation}` and `Interp/FreeOmega/{Translate,Cofinality}`
locally register structural measure/omega
operations to preserve the compiled signatures of their finite approximants.
The original contract snapshot detected these otherwise silently changed
arguments; it was not regenerated to accommodate the change.
`FiniteInternalJoint` locally registers its two structural law dependencies.
The operational Bernoulli/Von Neumann/rational-coin proofs and the interactive
Von Neumann service locally register structural operations for their internal
finite-approximation and bind-front calculations; their behavioral statements
retain explicitly observable operations. None of these local registrations
is exported to importers. Existing proof scripts are unchanged.

Unused native `NI` is removed only from the basic `PEutt` and first
`PTreeKernel` sections; the latter's `FO` starts after `ptree_primitive_kernel`.
No compiled argument list changes.

## Operation selector

`API/Behavior` defines `CanonicalBehavior MN` with exactly four fields:
`behavior_frontier`, `behavior_measure`, `behavior_mixed`, `behavior_omega`.
There are no Core/Bind/Omega/Fubini or external-realization laws in the record,
no projection instances, and no automatic conversion to other capabilities.

`canonical_peutt` unfolds to raw `PEutt.peutt` using these four fields.
It separately requests CoreLaws for the selected measure. The builder in
`API/BehaviorFreeOmega` is an ordinary definition, never a blanket instance.

| Registered adapter | Frontier | Measure/omega interpretation |
| --- | --- | --- |
| `API/EnumQ` | `FreeOmega EnumQ` | Observable |
| `API/SubEnumQ` | `FreeOmega SubEnumQ` | Observable |
| `API/SubEnumR` | `FreeOmega (SubEnumR R)` | Observable |
| Existing Gate M `Eq/Backend/MathComp/Direct` | `MathCompKernelMeasure R` | Native self-frontier |

EnumQ has an intentional route because weighted programs remain maintained
clients (including the Bernoulli factory). This does not make arbitrary
weighted EnumQ programs valid subprobability programs. No selector bypasses
the separate admissibility/modelability requirements for external soundness.

The registry is unique by audited project policy, not by a uniqueness theorem
about Rocq typeclasses. Clients may still explicitly choose a different
interpretation through raw `@peutt`.

## Checked routing and trust boundaries

Three independent files test ordinary imports, structural-first imports and
native-first imports. Each proves full definitional equality with the explicit
observable `@peutt` term for all three finite backends and arbitrary return
relation `A -> B -> Prop`, using only `reflexivity`. Each rejects a generic
blanket selector and checks that Gate M has not been loaded.

`StructuralRegistry` rejects automatic resolution of all ten structural
instances, verifies shared mixed inference, and verifies that deliberate local
registration works without leaking from its section.

The existing MathComp direct regression separately checks its full native
expansion. The two Gate M files and checker-relaxation policy are unchanged.
Only their exact dependency on `API/Behavior` is newly allowed; safe theory
does not import the direct adapter. The Gate M assumption audit records the two
new declarations separately from safe controls and retains its unsafe-hierarchy
reporting. This is not a universe-safe MathComp assembly claim.

## Preservation and local validation

`tools/audit_behavior_routing.py` compares against `04475b2`, not a newly
captured reference. It checks the exact registration-only structural change,
the two Context edits, scoped local registrations, preservation of existing
API/direct declarations, unchanged other theory files, and the four-route
registry. Its compiled mode independently replays the frozen source:

- 32 structural compiled bodies agree (not just theorem statements).
- 61 structural/basic compiled types and logical assumptions agree.
- 17 new safe definitions/probes obey the existing logical-axiom whitelist.

The original 505-contract snapshot and public glyph/bind facade definitions
remain frozen. The exact facade policy adds only the reviewed selector API;
the separate MathComp snapshot adds its selector and expansion regression,
with all pre-existing entries required to stay identical.

Local validation commands:

```sh
opam exec -- dune build
python3 tools/audit_behavior_routing.py --compiled --kernel
python3 tools/audit_assumptions.py --check
python3 tools/audit_api.py --surface-only
python3 tools/audit_soundness.py --check
python3 tools/audit_architecture.py --check
python3 tools/audit_mathcomp_direct.py --gate M
python3 -m unittest discover -s tools -p 'test_*.py'
```

The targeted 23-module joint kernel check covers the changed safe theory, selectors and
import-order/registry probes, with `-norec` (dependencies loaded, not recursively
rechecked). Gate M is excluded. No remote CI result is claimed.

Completed locally: full build and safe AllImports; 505 unchanged compiled
contracts; architecture/API/source/compiled soundness audits; 129 tool tests;
the frozen-source replay above; and the 23-module joint kernel check. The
separate Gate M audit passes for 32 direct endpoints plus six safe controls,
retaining unsafe-hierarchy flags. These results do not constitute a recursive
whole-library kernel audit or a universe-safe Gate M claim.

## Next gate — deliberately not done here

Move `≈ₚ / ≈ₚ[RR]` ownership to the canonical API, align public heterogeneous
`peutt_bind` with that relation using actual existing laws/corollaries, and run
the minimal `PTree + API/SubEnumQ` client with no extra implementation import.
Then introduce `≡ₚ / ≃ₚ` and migrate ordinary examples. Until then, the existing
public glyph is still the raw notation: the selector's guarantees apply to
`canonical_peutt`, not yet to every old `≈ₚ` occurrence.
