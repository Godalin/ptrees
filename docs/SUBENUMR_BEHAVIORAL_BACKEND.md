# SubEnumR relational and behavioral backend

Finite-real native laws instantiate the shared FreeOmega behavioral theory.
External validation is separate: see [generic qlift validation](GENERIC_QLIFT_VALIDATION.md)
and [SubEnumR joint realization](SUBENUMR_JOINT_REALIZATION.md), both completed.
The shared representation is described in [finite backends](FINITE_BACKEND_CONSOLIDATION.md).

## Native finite-real couplings

`Prob/Backend/SubEnumR/Coupling.v` completes the existing actual-joint
lifting. It does not replace it with support matching or a dual condition.
Given joints `j : A * B` and `k : B * C` with the same B marginal, the
composed joint enumerates all pairs of entries. Matching entries receive
weight `p * q / mass_B(b)`; nonmatching entries receive zero. The exact
finite-sum identities prove both marginals. A positive entry in either
joint forces positive shared atom mass, so cancellation is only used on
positive fibers. No default value, decidable equality on carriers, unit
total mass, or finite transport-existence premise is required.

Relational bind chooses the supplied finite joint at each related input
pair, uses zero outside that relation, and binds the input joint to those
joints. This uses the existing classical indefinite-description foundation,
not a new joint-existence axiom. The input joint's AE support discharges
the pointwise fiber obligation.

The new instances are:

- `SubEnumR_SemanticMeasureCoreLaws`;
- `SubEnumR_SemanticMeasureBindLaws`;
- `SubEnumR_SemanticMeasureAELiftLaws`;
- `SubEnumR_SemanticMeasureCouplingAELaws`.

The old foundational AE/Subprobability instances remain unchanged. Equality
coupling is equivalent to finite-expectation equality. AE transport is
proved using zero expectation of the indicator of the bad set, so duplicate
entries and zero-weight entries cause no representation restriction.

`Omega.v` supplies native order, totality and a bounded-expectation scalar
supremum predicate. It proves native order laws and total properness, but
does **not** claim native omega completeness: finite-support distributions
do not contain every increasing limit. Completion belongs to FreeOmega.

The independent native regression checks crossed graph composition,
heterogeneous bind, duplicate partial mass, zero-weight support restriction,
and a coupling on an empty carrier. It imports neither FreeOmega nor the
external OmegaVal model nor the rational backend.

## Generic completion and PTree client

`Examples/Probability/SubEnumRBehavior.v` instantiates the existing generic
FreeOmega capabilities: Core, Bind, AE Kleisli/countable/coupling, Order,
Omega, total properness, cofinality, OmegaAE, diagonal, Fubini and the mixed
bind/unit/node-bind/omega laws. These are typeclass assembly, not new proofs
of completion. Native `SemanticOmegaLaws (SubEnumR R)` is deliberately absent.

The same module instantiates actual, heterogeneous-return PTree endpoints:
`pstruct -> peutt`, `pstrong -> peutt`, complete stable-hitting existence,
arbitrary eventful behavioral bind, and iter unfolding. It proves a crossed
sampling equality using the new native graph coupling, promotes it through
PStrong to peutt, and composes it with an infinite visible service using a
square-root-weight native coin. No rational backend, MathComp kernel backend
or external OmegaVal model is imported. In particular, ordinary behavioral
reasoning does not depend on external validation or a supplied gluing law.

This is the maintained behavioral profile, not a claim that every optional
native-reflection or recovery certificate is automatically available.
External qlift joint realization and stable-hitting modelability/adequacy are
also proved, but remain validation-side results, not behavioral prerequisites.
See [FreeOmega soundness](FREEOMEGA_SOUNDNESS.md).

## Verification and assumption boundary

The native finite constructions use the existing classical/extensional
foundation, not new probability axioms. Concrete clients retain the logical
dependencies of the generic theorems they instantiate; inspect their current
compiled records rather than treating old per-stage assumption lists as current.
Use [Maintained verification](AUDITING.md) for the build, contract registry,
source-safety and separate Gate M checks. Historical build counts and stage
validation logs remain in Git.
