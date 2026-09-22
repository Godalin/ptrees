# SubEnumR relational and behavioral backend

Baseline: `7e75db0`. Local verification only; CI and MathComp universe work
are outside this increment. No existing DS1--DS5 proof or public facade changes.

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

Native checkpoint verification: full local build/AllImports; architecture,
API and source audits; all 50 tool tests; all 505 frozen compiled signatures
and per-endpoint assumptions unchanged; joint targeted `coqchk -norec` of
Coupling, Omega and SubEnumRRelational passed. The five principal new
coupling/instance endpoints were separately checked against the existing
logical-axiom whitelist: only MathComp boolp extensionality and classical
indefinite description occur, with no new semantic assumption.

## Completion acceptance target

The next checkpoint must instantiate the existing generic FreeOmega
capabilities and actual PTree endpoints. No copied completion proof and
no `SemanticOmegaLaws (SubEnumR R)` assumption is acceptable. General qlift
external joint soundness is a separate later strengthening; the SubEnum
DS5 theorem is not silently generalized by these native instances.
