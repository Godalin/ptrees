# Phase 3 — SubEnumR uses the shared finite carrier

Accepted starting point: `aac7516` (Phase 2). This gate migrates **only the
real native backend**, not EnumQ/SubEnumQ, the generic semantics, or MathComp.
CI and environment changes remain out of scope.

## Actual representation, not a conversion layer

In `Prob/Backend/SubEnumR/Representation.v`:

```coq
Definition SubEnumR (A : Type) := FiniteSubdist R A.
Definition subenumR_raw {A} (mu : SubEnumR A) : list (R * A) :=
  finite_enum_raw (finite_subdist_enum mu).
```

`R` remains the existing `realType` backend parameter. Common's weaker
`numDomainType` boundary is unchanged. SubEnumR no longer declares a record,
constructor or eliminator; `Build_SubEnumR` and `SubEnumR_rect` are absent.
There is no compatibility constructor hiding a second carrier.

The sign invariant lives in the shared `FiniteEnum` component. The established
`subenumR_nonnegative` name remains an accessor **theorem**, not a record
field. It reads `finite_enum_nonnegative (finite_subdist_enum mu)`.
Likewise the mass-bound theorem uses `finite_subdist_mass_bound`.

The native operations `subenumR_ret`, `subenumR_zero`, and `subenumR_bind`
directly specialize the shared smart constructors. `subenumR_of_list` is the
custom-list smart constructor, specializing `finite_subdist_of_list`.
Neither operation closure nor invariant proofs are copied into the backend.
The coin constructor supplies its two list-specific validity proofs once.

Native `subenumR_eq`, `subenumR_ae`, and `subenumR_lift` retain their exact
definitions and meanings. Actual finite joints, gluing, relational bind,
domain validation and external joint realization stay backend-owned; Common
does not acquire these interfaces.

## Finite algebra reuse

`real_enum_expect` and `real_enum_nonnegative` now specialize the shared
operations. The ten existing finite expectation laws are one-line uses of
their Common counterparts, including ext/zero/add/scale/mono/nonnegative,
AE monotonicity, append, weight scaling and bind expectation. Native bind
unit/associativity proofs similarly use the shared expectation laws.

These are the established native API names with unchanged theorem types,
not a second recursive implementation. There is no `Fixpoint` or induction
proof left in Representation.v. Two definitional nil/cons equations allow
clients to compute expectations without knowing the shared recursion's name.

Domain continuity and coupling proofs that previously unfolded the old
Fixpoint now rewrite those equations. Their theorem statements are unchanged.
Gluing uses `subenumR_of_list` in place of the removed record constructor.
The existing duplicate/zero-weight regression does the same.

`SubEnumR/RationalEmbedding.v` necessarily adapts the target constructor and
one expectation computation. Its source-side Q representation and scalar map
are untouched: it still consumes existing SubEnumQ/nnQ data. Generic ordinary
scalar transport is Phase 6, not a claim of this migration.

## Regression evidence

`Regression/Backend/SubEnumRShared.v` establishes by `reflexivity`:

```text
SubEnumR R A = FiniteSubdist R A
native ret / zero / bind = shared ret / zero / bind
native expectation = shared expectation
native raw list = the nested shared raw list
```

Shared values can be passed directly into the native API and vice versa,
with no rebuilding, casting or representation proof. A shared custom list
with a zero-weight branch is consumed by native AE and a non-diagonal actual
joint coupling. Shared bind is immediately accepted by the native
subprobability interface.

The generic FreeOmega core/bind/omega profile is inferred with the visible
carrier `FreeOmega (FiniteSubdist R)`. Native finite omega-completeness is
still rejected. A high-universe carrier containing `Type@{u}` supports native
bind with shared return values under normal universe checking.

Existing real-weight coupling regressions, eventful behavioral bind/iter,
infinite services, invalid-intermediate qlift validation and external actual
joint realization are retained and rebuilt, not replaced with new smoke tests.

## Preservation gate

`audit_subenumR_migration.py` has two independent checks:

1. Source conservation against `aac7516`. All old tracked files remain exact
   except Representation.v, explicitly enumerated proof/constructor edits in
   Coupling.v / Domain.v / RationalEmbedding.v / SubEnumRRelational.v, one
   AllImports insertion, registration of the new regression, and the generated
   architecture report. The native relations and old Representation theorem
   statements are compared separately. Common, all rational modules, all
   FreeOmega validation modules, and MathComp remain byte-identical.
2. A pre-migration compiled snapshot of **161** SubEnumR constants, covering
   every explicitly declared native/validation constant plus the behavioral
   and external joint regressions. Actual types and `Print Assumptions` are
   compared exactly modulo printing whitespace; no premise or assumption
   normalization is allowed. A SHA-256 check prevents refreshing the snapshot
   during migration. Capture mode refuses changed old theory sources.

The 505-entry original contract snapshot and the Phase 1 / Phase 2 audit
programs are unchanged. Those earlier phase-specific checks still describe
their frozen checkpoints; they have not been loosened to accept Phase 3.

The new broader behavioral snapshot explicitly records pre-existing
`RelationalChoice.relational_choice` and
`ClassicalUniqueChoice.dependent_unique_choice` dependencies of behavioral
bind. They are identical before and after migration, not newly introduced
assumptions. The narrower external-soundness whitelist is not expanded;
its independent audit remains in force.

Repository counts: 280 theory modules (278 Gate S / 2 Gate M), 73 regression
modules, 4115 direct local Require edges, 18 Python tool files, 91 tool tests.
Only one new theory module is added, the shared-carrier regression.

## Local verification

Completed:

- Full `dune build`, including safe AllImports and all existing regressions.
- Phase 3 exact source/adaptation check.
- All 161 pre-migration real-backend compiled types and assumptions unchanged.
- All 505 existing mainline compiled contracts and assumptions unchanged.
- Architecture/API checks and all 91 tool tests, including migration mutation
  tests and rejection of post-migration baseline recapture.
- Long-term soundness audit: 199 frozen exact contracts, 36 generic
  validation, 18 finite-real realization and 80 native MathComp endpoints;
  unchanged logical whitelist and source-safety/capability policy.
- The 15-module targeted joint `coqchk` scope below completed successfully.

Commands:

```sh
opam exec -- dune build
python3 tools/audit_subenumR_migration.py
python3 tools/audit_assumptions.py --check
python3 tools/audit_soundness.py --check
python3 tools/audit_architecture.py --check
python3 tools/audit_api.py --check --surface-only
python3 -m unittest discover -s tools -p 'test_*.py'
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Prob.Backend.SubEnumR.Representation \
  -norec PTree.Prob.Backend.SubEnumR.Measure \
  -norec PTree.Prob.Backend.SubEnumR.Coupling \
  -norec PTree.Prob.Backend.SubEnumR.Omega \
  -norec PTree.Prob.Backend.SubEnumR.Domain \
  -norec PTree.Prob.Backend.SubEnumR.RationalEmbedding \
  -norec PTree.Prob.Backend.SubEnumR.FreeOmega.Validation \
  -norec PTree.Prob.Backend.SubEnumR.FreeOmega.RelationalValidation \
  -norec PTree.Prob.Backend.SubEnumR.FreeOmega.CountableSupport \
  -norec PTree.Prob.Backend.SubEnumR.FreeOmega.JointRealization \
  -norec PTree.Regression.Backend.SubEnumRShared \
  -norec PTree.Regression.Backend.SubEnumRRelational \
  -norec PTree.Regression.Backend.SubEnumRBehavior \
  -norec PTree.Regression.Probability.SubEnumRJointRealization \
  -norec PTree.Regression.Infrastructure.AllImports
```

The targeted joint kernel scope is the ten `Prob/Backend/SubEnumR` modules,
SubEnumRShared, SubEnumRRelational, SubEnumRBehavior,
SubEnumRJointRealization, and safe AllImports. This uses `coqchk -norec`:
it checks those 15 module bodies while trusting compiled dependencies, not
the whole dependency closure. Neither Gate M module is included.

## Stop point

SubEnumR now uses the shared record. EnumQ/SubEnumQ still use their accepted
rational representations, and `nnQ` retirement, Q-to-R common scalar transport
and further optional deduplication remain later phases. No MathComp change,
new probability capability, new axiom or trust exception is part of Phase 3.
