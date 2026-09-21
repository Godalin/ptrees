# DS2.5: native expectation dependency hygiene

Frozen source baseline: **DS2 accepted at `bc8f9d2`**. This follow-up changes
ownership/imports only, not mathematical definitions, statements or proofs.
Stop for acceptance before DS3. No quotient soundness or stable-hitting
denotational adequacy theorem is introduced here.

## Dependency direction

```text
SubEnum/Expectation (finite weighted expectation facts)
       ├──> SubEnum/Domain (native OmegaVal adapter)
       └──> SubEnum/FreeOmega/Upper* (raw evaluator mathematics)
                  both feed
       SubEnum/FreeOmega/{Admissibility,DomainSoundness}
```

Arrows mean “used by”. In particular **Upper files do not import Domain**:
the external validation layer remains outside the maintained reasoning
infrastructure. The architecture checker enforces this existing boundary
and the new, transitive native expectation/domain-to-FreeOmega prohibition.

Only 27 declarations, the finite dependency closure used by the native
adapter, move into `Prob/Backend/SubEnum/Expectation.v`:

- finite weighted expectation, bounds, zero/mass, bind/map algebra;
- native coupling/AE test inequalities and their finite helper chain;
- scalar supremum facts needed for finite expectation/countable-sup exchange.

They remain together under SubEnum because the native coupling bridge uses
both validated SubEnum and its Enum representation. No second backend-wide
reorganization is attempted. `countable_upper_swap`, raw evaluator
continuity and every FreeOmega-specific theorem remain in the Upper files.
The adapter's own finite scale/add helpers are unchanged.

The Upper files export the relocated facts rather than defining compatibility
wrappers. Unqualified names remain available; fully qualified names of the
27 moved declarations change to `PTree.Prob.Backend.SubEnum.Expectation.*`.
An explicit local notation in UpperExpectation restores the pre-extraction
Section-local `@countable_upper_ge` application spine. No proof body is edited.

## Conservation checks

`tools/audit_ds25.py` reconstructs the expected tree from `git archive
bc8f9d2`. Extraction copies exact source slices; the remaining source must
match byte-for-byte, including comments, imports and whitespace, except for
the enumerated import/export, local notation and AllImports insertions.
All other `.v` files must be identical. There are 228 baseline modules and
229 after extraction; no baseline module is deleted.

In particular this freezes OmegaVal, MeasureModel, admissibility, the
AE/pselect implementation, raw FOLub, qlift, Eq/Interp and all regressions.
Historical Gate/DS snapshots are not regenerated to hide differences.

`DOMAIN_DS25_BEFORE.json` was captured from the compiled `bc8f9d2` tree
**before editing any `.v` file**. It covers all 55 named definitions,
fixpoints and theorems in the three Upper files plus SubEnum/Domain. The
post-migration check queries their actual compiled types and logical
assumptions. Only the exact 27-name relocation and printer whitespace are
normalized; premises, conclusions, axiom names/types and string literals
are not removed. Negative unit tests reject proof/layout edits, modifications
to frozen mathematics, lost contracts and new axioms.

The accepted DS2 51-endpoint report is likewise checked with that explicit
relocation map, not overwritten. DS1a's 37, DS1b's 37 and the mainline's 306
endpoint snapshots remain separate checks.

## Validation

All checks below passed locally:

- `opam exec -- dune build`, including AllImports;
- `python3 tools/check_aggregate.py`: 228 imported modules;
- `python3 tools/audit_architecture.py --check`: ownership and both
  transitive isolation boundaries;
- `python3 tools/audit_ds25.py --check`: exact 228-to-229 source extraction
  and all 55 compiled Upper/native contracts;
- `python3 tools/audit_domain.py --check`: DS1a 37 endpoints;
- `python3 tools/audit_domain_measure.py --check`: DS1b 37 endpoints;
- `python3 tools/audit_domain_soundness.py --check`: DS2 51 endpoints;
- `python3 tools/audit_public_capabilities.py --check`: mainline 306 endpoints;
- `python3 tools/audit_capabilities.py --check`: original 25-endpoint baseline;
- `python3 -m unittest discover -s tools -p 'test_*.py'`: 52 tests;
- `git diff --check`.

The following **joint** kernel check completed with exit status 0:

```sh
opam exec -- coqchk -silent -R _build/default/theories PTree \
  PTree.Prob.Backend.SubEnum.Expectation \
  PTree.Prob.Backend.SubEnum.FreeOmega.UpperExpectation \
  PTree.Prob.Backend.SubEnum.FreeOmega.UpperCoupling \
  PTree.Prob.Backend.SubEnum.FreeOmega.UpperContinuity \
  PTree.Prob.Backend.SubEnum.Domain \
  PTree.Prob.Backend.SubEnum.FreeOmega.Admissibility \
  PTree.Prob.Backend.SubEnum.FreeOmega.DomainSoundness \
  PTree.Regression.Probability.FreeOmegaDomain
```

These eight requested modules and their dependencies are the targeted
DS2.5 kernel scope, **not** whole-library Gate D verification. No new
semantic or logical axiom is introduced. No remote CI result is claimed.

DS3 remains pending acceptance of this follow-up. Its planned equality
route reuses `free_omega_qlift_eq_upper` on raw terms, then transports
admissibility and obtains `oval_eq`; no structural induction on qlift is
planned or implemented here.
