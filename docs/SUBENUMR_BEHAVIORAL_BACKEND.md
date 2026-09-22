# SubEnumR relational and behavioral backend

The next follow-up is tracked separately in
[native-parametric qlift validation](GENERIC_QLIFT_VALIDATION.md): shared
bounded-test/dual constraints, without a generic joint-existence claim.

Baseline: `7e75db0`. Local verification only; CI and MathComp universe work
are outside this increment. No existing DS1--DS5 proof or public facade changes.

Checkpoints: `fc15702` proves native relational infrastructure; the follow-up
commit contains only its generic completion/PTree clients and audit/docs.

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

## Generic completion and PTree client

`Regression/Backend/SubEnumRBehavior.v` instantiates the existing generic
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

This is the maintained behavioral capability profile, not a claim that
every optional recovery, native-reflection or external soundness capability
has been instantiated. In particular general qlift external joint soundness
remains a separate later strengthening; the SubEnum DS5 theorem is not
silently generalized by these native instances. The next useful step is a
native-independent raw-qlift bounded-test bridge, before attempting general
external joint realization. MathComp mathematical/universe gaps are unchanged.

## Final verification and assumption boundary

- Full local build and AllImports passed with all 260 modules together.
- Architecture, API, soundness-source checks and all 50 tool tests passed.
- All 505 frozen compiled signatures and per-endpoint assumptions are unchanged.
- All 27 new completion/behavior endpoints were inspected by `Check @` and
  `Print Assumptions`. No supplied native gluing, native omega completeness,
  transport existence, or new semantic class occurs in their signatures.
- Joint targeted `coqchk -silent -norec` of Coupling, Omega,
  SubEnumRRelational and SubEnumRBehavior passed. This is not a recursive
  whole-library kernel audit.

The native proofs and completion clients stay within the existing Domain/
native logical-axiom whitelist. Two PTree bind clients additionally inherit
`RelationalChoice.relational_choice` and
`ClassicalUniqueChoice.dependent_unique_choice` from the **already frozen**
`Eq.FreeOmega.Bind.peutt_bind`. Their assumptions were checked against that
exact existing endpoint as well as the native whitelist; neither whitelist
nor the old contract snapshot was widened. These are inherited logical
foundations, not new probability or backend assumptions.

No new `Axiom`, `Parameter`, `Admitted`, `Class`, unsafe universe setting,
external-model dependency in native theory, or public API change was added.
CI and dependencies were not inspected or modified.
