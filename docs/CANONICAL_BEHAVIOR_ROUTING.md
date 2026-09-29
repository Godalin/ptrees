# Canonical behavioral routing

## Why operation selection matters

The same raw `FreeOmega MN A` supports two relation interpretations:

| Interpretation | Equality/lifting | Role |
| --- | --- | --- |
| Structural | `free_omega_lift` | Internal constructor-sensitive proofs |
| Observable | `free_omega_qlift` | Canonical behavioral theory |

Choosing only the frontier carrier therefore does not determine `peutt`.
The canonical route fixes operations explicitly; it does not change either
relation or turn the raw syntax into a different quotient datatype.

## Selector and owners

`Eq/Canonical` defines `CanonicalBehavior MN` with four fields:
`behavior_frontier`, `behavior_measure`, `behavior_mixed`, `behavior_omega`.
No probability law is bundled, and projections are not capability instances.
`canonical_peutt` expands to raw `PEutt.peutt` with these operations and
separately requires Core laws for the chosen measure.

`Eq/FreeOmega/Canonical` provides the ordinary builder, not a blanket instance.

| Registered adapter | Frontier | Interpretation |
| --- | --- | --- |
| `Eq/Backend/EnumQ` | `FreeOmega EnumQ` | Observable |
| `Eq/Backend/SubEnumQ` | `FreeOmega SubEnumQ` | Observable |
| `Eq/Backend/SubEnumR` | `FreeOmega (SubEnumR R)` | Observable |
| Gate M `Eq/Backend/MathComp` | `MathCompKernelMeasure R` | Native self-frontier |

The weighted EnumQ route does not imply that arbitrary weighted programs are
subprobabilities. External soundness still requires admissibility/modelability.
Route uniqueness is enforced by project policy, not a uniqueness theorem about
typeclasses. Experts may explicitly select another interpretation through raw
`@peutt`. Public `≈ₚ` notation belongs to `Eq/Canonical`; see
[public modules](PUBLIC_MODULES.md).

## Structural and trust boundaries

Auxiliary structural measure/omega operations and laws are registered locally,
not as competing global behavioral defaults. Proofs needing them may opt in
locally. `FreeOmegaMixedMeasure` remains shared: its sampling operation is the
same for both interpretations.

Three independent import-order clients check full definitional equality with
observable `@peutt` for all finite routes, including heterogeneous return
relations. They reject a blanket selector and ensure Gate M is not loaded.
`StructuralRegistry` checks that automatic search does not select structural
instances and that deliberate local registration works without leaking.

MathComp's native expansion is checked separately in Gate M. Its locally
relaxed universe checking is not inherited by safe theory or ordinary public
imports. [AUDITING](AUDITING.md) describes the maintained registry, source and
compiled-contract checks; no historical source-replay tool is required.

The accepted routing and notation migrations (`a95734e`, `33cb5d8`) remain
available in Git. They are provenance, not unfinished API gates.
