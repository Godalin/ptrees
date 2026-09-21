# Cleanup B: conservation and validation

Baseline: **`5c1a0df`**, following the accepted Cleanup A inventory
(`381902d`) and aggregate-order fix. This cleanup implements only that
inventory. It adds no theory and does not start MathComp self-model work.

## Counts and disposition

| Item | Baseline | After cleanup |
| --- | ---: | ---: |
| Coq modules | 252 | 245 |
| Regression modules, including aggregate and fixture | 69 | 62 |
| Formal/application modules outside Regression | 183 | 183 |
| Python files in tools | 25 | 7 |
| Documents/data in docs | 45 (44 + Cleanup A inventory) | 8 |
| Public/helper compiled endpoint contracts | 306 | 306 |
| Included capability probes | 25 | 25 |
| Formal soundness endpoint contracts | 199 across phase scripts | 199 in consolidated manifest |

No whole formal module is deleted. Four historical forwarding `Export`
edges become ordinary imports; actual clients import StableHittingRelation
or native SubEnum/Expectation explicitly. Canonical owners, theorem names,
definitions, proofs and curated API remain unchanged. Legacy/Rbase is retained.

The approved 11 old regression files are removed **after** relocation:

| Old family (under Regression) | Destination |
| --- | --- |
| Backend/FreeOmegaUpperExpectation, Continuity, Observation, Quotient | Backend/FreeOmegaUpperContracts, four nested test groups |
| Probability/CountableTransport, CountableTransportExistence | Probability/CountableCoupling |
| Probability/FreeOmegaQuotientDomain, FreeOmegaRelationalDomain, FreeOmegaJointDomain | Probability/FreeOmegaSoundness |
| Semantics/HittingDivergence | Semantics/CanonicalPartialDivergence.HittingDivergenceTests |
| Semantics/PEuttNotation | Semantics/PublicSemanticFacade.PEuttNotationTests |

Shared raw samples, geometric retry and duplicate/invalid codes move into
Regression/Fixtures/FreeOmegaSamples. This removes the would-be cycle between
combined coupling and soundness tests. Its geometric validity proof is only
relocated; a local notation in the client restores the old section-parameter
view. It is not a new theorem or API. Negative import tests execute before
loading the corresponding implementation/fixture, not after a bulk import.

Every other inventory KEEP decision is retained, notably OmegaValMeasure's
Domain-only boundary, raw FreeOmega escaping mass versus matrix escaping mass,
FreeOmegaLimitSafety, higher-universe tests, and all FiniteInternal/Recovery/
residual infrastructure. Mainline and final soundness closures are unchanged
in their separation from that auxiliary branch.

## Proof and contract conservation

The one-off comparison against `git show 5c1a0df:<path>` checked:

- All **183** non-Regression module texts are identical after removing nested
  comments, complete Require commands and whitespace. Nothing removes theorem
  statements, Section contexts, class fields, definitions or proof bodies.
- The **14** affected old regression sources (11 removed plus three receiving/
  fixture-source files) map to **seven** retained/new targets, including the
  shared fixture. The multisets of named declarations and all **125** `Proof...`
  blocks agree, including multiplicity. Statements, definitions and proof
  blocks compare byte-for-byte after comment removal, not a tactic or theorem
  normalization. All other KEEP regressions agree modulo explicit imports;
  AllImports is separately checked for sorted complete coverage.
- Existing facade texts are frozen separately. The unified compiled manifest
  was captured **before** removing exports or rebuilding changed sources.
  Its 306 public/helper and 199 formal DS endpoints match the union selected
  by the old scripts. The one native forwarded name is explicitly canonicalized:
  `UpperCoupling.subenum_lift_real_expect` becomes
  `SubEnum.Expectation.subenum_lift_real_expect`.
- The post-change compiled query compares all **505** complete types and
  `Print Assumptions` outputs exactly in the same module-loading context.
  No shortened capability-count comparison or automatic baseline refresh occurs.
- All **505** endpoints also agree with the old accepted phase reports and
  Gate C after-snapshot retrieved from `5c1a0df`, after the explicitly recorded
  Prob/DS2.5 ownership relocations and full-versus-short owner qualification
  used by Coq's printer. This one-off historical comparison reports zero
  differences; those normalizations are not part of the new runtime checker.

Stage-specific regression snapshots are replaced by retained, compiled test
proofs and named coverage in CONTRACT_POLICY, not by declaring the source
programs sound by fiat. In particular the invalid FOQLComp middle, raw invalid
Lub, partial mass, no-mass-escape and high-universe probes remain actual proofs.
The soundness logical-axiom whitelist is unchanged. Phase-specific source
insertion/move audits and their tests belong to their accepted git revisions;
they are no longer replayed against a deliberately reorganized repository.

## Maintained validation

```sh
python3 tools/audit_architecture.py --aggregate-only
opam exec -- dune build
python3 tools/audit_architecture.py --check
python3 tools/audit_api.py --surface-only
python3 tools/audit_soundness.py --source-only
python3 tools/audit_assumptions.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
python3 tools/audit_api.py --surface-only --kernel
git diff --check
```

Local results: **all passed**.

- Full `dune build`, including AllImports (and a final no-op rebuild).
- Aggregate coverage/order/uniqueness, live architecture and transitive boundaries.
- Curated API and source-safety/independent-model contracts.
- Exact 505 compiled types and per-endpoint logical assumptions; historical
  report comparison also has zero differences after the declared relocations.
- All 39 maintained audit-tool unit tests.
- Formal/regression source conservation and local Markdown link checks.
- Targeted 16-module joint `coqchk`, exit status zero.
- `git diff --check`.

The joint kernel check explicitly selects 16 module bodies with `-norec`,
including AllImports, universe/facade boundaries, all merged families,
domain/measure/hitting/irrational-limit tests and finite real transport.
Dependencies are loaded in the shared universe context, **not recursively
proof-checked**. No `-admit`, disabled universe check or explicit VM checker
override is used. Coq emitted its standard warning that the native compiler
is disabled and native conversion falls back to VM conversion; the check
completed normally with that default behavior. This is not the deferred
whole-library Gate D audit.

CI now calls the consolidated tools and uses the printed-contract dependency
profile documented in ARCHITECTURE.md. The previous completed CI installation
log used HB 1.10.1 / ExtLib 0.13.1, versus the local snapshot's 1.8.1 / 0.13.0.
Pinning the CI audit profile avoids confusing dependency-generated type/name
changes with a repository contract change; package compatibility bounds are
unchanged. No remote build result for the new profile is claimed here.

Removed phase tools and reports are recoverable from `5c1a0df`. Their final
claims now live in ARCHITECTURE.md, FREEOMEGA_SOUNDNESS.md and the two contract
files, while focused Interp and universe explanations remain. No remote CI
success is inferred from local validation. Cleanup B ends at review; MathComp
self-model and the next generic soundness design require a separate stage.
