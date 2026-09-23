# Finite discrete backend consolidation

## Current representation (final carrier migration)

The production definitions now specialize the shared invariant-bearing records:

```text
EnumQ A       = FiniteEnum rat A
SubEnumQ A    = FiniteSubdist rat A
SubEnumR R A  = FiniteSubdist R A
```

Coefficients are ordinary scalars. Nonnegativity is a property of the whole
finite list; SubEnumQ/SubEnumR additionally carry the mass-at-most-one proof.
List order, repeated atoms and zero entries remain observable at the raw-data
level. No carrier coerces silently to a list: use `enumQ_raw`, `subenumQ_data`
or the corresponding shared projection. `subenumQ_raw` returns a checked
EnumQ, not an unvalidated list. Constructors with arbitrary rational weights
take explicit nonnegativity proofs, replacing the former implicit nnQ proof.

Both rational/real bind use the shared finite construction. Q-to-R transport
uses `finite_subdist_map_weights` with `ratr`; it is not a restore/repack
pipeline. The deprecated subtype lives only in `Prob/Legacy/RatSubTypes.v`.
Historical migration regressions may import it, but native backends and
Examples may not. The historical old/shared isomorphism is a test fixture,
not a production conversion layer.

Shared list algebra, atoms, positions, pruning, finite presentation and indexed
bind machinery are reused without moving coupling semantics into Common.
The rational backend retains its actual finite joint and indexed lifting
semantics; FreeOmega and the PTree relation hierarchy are unchanged.

Raw-list equality is the ordinary algebra API. Some exact observation-witness
clients additionally need equality of checked records. The optional
`Common/FiniteRecordExtensionality.v` proves this using existing functional
extensionality and decidable equality of Boolean proofs. It is not imported
by native finite algebra or instances, and does not assume general proof
irrelevance. Its logical dependency is explicit.

`tools/audit_finite_consolidation.py` is the migration gate frozen at
`5f6b414`, not a prohibition on later generic theory improvements. It protects
125 generic/MathComp/real-backend source files byte-for-byte against `1cba6c5`
and compares all 505 frozen compiled endpoints. Only reviewed definition-owner
relocations and the definitional rat carrier projection are normalized; added
premises or logical assumptions are rejected. Snapshot refresh is allowed only
after that comparison. The old Phase 0–4 preparation audits below remain
historical exact checks at their named commits, not constraints to relax for
the new representation.

Phases 0–7 are now implemented. The complete client rebuild, preservation
checks and targeted kernel validation passed locally; see
[the final migration report](FINITE_BACKEND_FINAL_MIGRATION.md) for the exact
scope, commands and remaining trust qualifications. The sections below record
the historical naming gate, not the current implementation status.

## Historical naming checkpoint

Accepted pre-refactor baseline: `ba509e1`. CI and environment changes are out
of scope. MathComp mathematics and the exact two-file Gate M trust boundary
are not being redesigned.

## Target and phase boundaries

The final target is ordinary scalar lists with two container-level invariants:
`FiniteEnum R A` carries nonnegative coefficients; `FiniteSubdist R A` adds
mass at most one. `EnumQ`, `SubEnumQ` and `SubEnumR R` will specialize those
records at rational/real scalars. No generic nonnegative scalar subtype,
new semantic class or new axiom is planned. Finite carriers remain separate
from their FreeOmega completion; direct MathComp stays a different model.

The migration is deliberately split into separate commits:

0. Freeze `ba509e1` and its contracts.
1. Pure naming: `Enum` / `SubEnum` become `EnumQ` / `SubEnumQ`.
2. Introduce shared finite weighting/subdistribution algebra.
3. Migrate SubEnumR to the shared records.
4. Migrate rational carriers off `nnQ`.
5. Mark `nnQ` legacy and enforce the maintained representation boundary.
6. Express rational-to-real transport through generic scalar mapping.
7. Deduplicate only obviously shared finite algebra.

## Phase 0/1: naming gate

This gate changes names, not representations. In particular **EnumQ still
stores `nnQ` coefficients at this intermediate checkpoint**. SubEnumQ is
still its existing bounded wrapper, and SubEnumR retains its existing record.
The shared `FiniteEnum` / `FiniteSubdist` representation is not yet installed.

Naming rules cover native module paths, specialized API/Eq/Semantics/Interp
paths, definitions, instances, tests and references:

- `Prob/Backend/Enum/` becomes `Prob/Backend/EnumQ/`.
- `Prob/Backend/SubEnum/` becomes `Prob/Backend/SubEnumQ/`.
- Rational identifiers use `EnumQ` / `SubEnumQ` and `enumQ_` / `subenumQ_`.
- `SubEnumR`, `subenumR_*`, `real_enum_*`, unrelated MathComp enumeration
  operations and generic FreeOmega/PTree definitions retain their names.
- Independent legacy `Prob/Legacy/Discrete.v` remains byte-identical; its
  historical real-weight `Enum` is not the maintained rational backend.
- No forwarding modules or old-name compatibility aliases are added.

`audit_finite_backend_rename.py` reads the frozen git archive and reconstructs
every expected file, including comments, imports and proof bodies. Rocq
sources must match exactly after the explicit rename, with only sorted
AllImports as a further transformation. No theory modules may be added or
removed. The module/edge counts must remain 276 / 4095.

Compiled snapshots are transformed from the frozen snapshots, not accepted
anew. Longer identifiers can change Coq's line wrapping: any resulting
snapshot refresh is allowed only after verifying identical renamed tokens,
including assumptions and Gate M unsafe flags. Proofs, endpoint premises,
logical-axiom whitelist and source-safety policy cannot be weakened to pass.

Baseline verification passed before renaming: 505 exact compiled contracts;
199 frozen soundness contracts; 36 generic, 18 finite-real and 80 native
MathComp validation endpoints, all with the existing logical whitelist.
The accepted baseline has 276 theory modules (274 Gate S / 2 Gate M),
71 regression modules, 4095 direct local import edges and 12 Python tool
files. Its recorded tool suite has 69 tests. Phase 1 keeps every theory
module, moves 59 module paths, and adds only a migration audit and its seven
unit tests (14 Python files / 76 tests). The two exact Gate M files and
their 30 direct endpoints plus 6 safe controls remain separately audited.

## Verification commands

```sh
opam exec -- dune build
python3 tools/audit_finite_backend_rename.py
python3 tools/audit_architecture.py --check
python3 tools/audit_api.py --check --surface-only
python3 tools/audit_assumptions.py --check
python3 tools/audit_soundness.py --check
python3 tools/audit_mathcomp_direct.py --gate M
python3 -m unittest discover -s tools -p 'test_*.py'
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Prob.Backend.EnumQ.Representation \
  -norec PTree.Prob.Backend.EnumQ.Measure \
  -norec PTree.Prob.Backend.SubEnumQ.Measure \
  -norec PTree.Prob.Backend.SubEnumR.RationalEmbedding \
  -norec PTree.Prob.Backend.SubEnumQ.FreeOmega.JointSoundness \
  -norec PTree.Eq.Backend.StableHittingDomainSubEnumQ \
  -norec PTree.Regression.Backend.SubEnumQRegression \
  -norec PTree.Regression.Backend.SubEnumRBehavior \
  -norec PTree.Regression.Probability.SubEnumRJointRealization \
  -norec PTree.Regression.Infrastructure.AllImports
```

The phase-specific source-conservation check is for Phase 1 only. Later
representation phases must establish their own preservation gates rather
than weakening this naming-only claim. No later phase is implied complete
by a successful rename.

The joint kernel command checks those ten safe module bodies while trusting
compiled dependencies. It neither claims a recursive whole-library audit nor
includes either universe-unchecked Gate M module.

## Phase 0/1 local validation results

- Full `dune build`, including AllImports: passed.
- Exact source conservation: all 276 modules passed; 59 paths relocated,
  no theorem/proof changes beyond names and aggregate sorting.
- Architecture and API surface: passed; 4095 direct edges and the
  274 safe / 2 Gate M split are unchanged.
- All 505 frozen compiled contracts: passed after systematic renaming;
  snapshot line wrapping was refreshed only after token-for-token comparison
  with the renamed baseline, with assumptions included.
- Gate M: 30 direct endpoints and 6 safe controls passed their separate
  type/assumption/unsafe-flag audit. This is not a universe-checked claim.
- All 76 tool unit tests: passed.
- Soundness audit: 199 frozen exact contracts, 36 generic validation,
  18 finite-real realization and 80 native MathComp endpoints passed;
  the existing logical-axiom whitelist and source-safety contracts are unchanged.
- The ten-module targeted joint `coqchk` command above: passed.

The inherited trailing space in the renamed EnumQ representation proof is
deliberately retained under the exact-source rule; this phase does not claim
a whitespace-clean `git diff --check`. No CI run or environment change is
part of this verification.

Only the baseline and naming phases are complete. Shared records, backend
representation migration, ordinary-scalar transport and retiring maintained
`nnQ` usage remain Phase 2 onward, not results of this commit.
