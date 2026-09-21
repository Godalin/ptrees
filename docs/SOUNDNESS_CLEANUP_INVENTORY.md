# Soundness Cleanup A — inventory and proposed disposition

Baseline: **`2dbba82`**, DS1–DS5a accepted. This document is the entire
Cleanup A change. Every disposition below is a proposal for review, not an
executed deletion or authorization to start Cleanup B.

## 1. Scope, evidence and baseline counts

Preserve mathematics; reduce migration scaffolding; retain semantic negative
tests and long-term contract audits. Do not redesign FreeOmega, admissibility,
OmegaVal, qlift, stable hitting, transport, or any accepted proof structure.
No MathComp-native soundness, qlift completeness or new public Domain helper.

The inventory uses tracked sources at the baseline, declaration/import scans,
the actual `.PTree.theory.d` graph via `audit_architecture.graph()`, and reverse
clients excluding AllImports. A dependency edge is evidence of loading, not
proof that a declaration is used. In particular, zero clients never suffices
to delete a regression or a maintained theorem.

| Baseline item | Count |
| --- | ---: |
| Coq modules | 252 |
| Regression modules, including AllImports | 69 |
| Other Coq modules | 183 |
| Python files in tools (20 entry/helper scripts + 5 test files) | 25 |
| Tracked files in docs before this inventory | 44 |
| Non-declaration modules found by the scan | 6 |
| Pure old-path compatibility modules confirmed deletable | 0 |

The following inspections were run, without modifying their inputs:

- Ownership and transitive dependency audit: passes at this baseline.
- AllImports contains all 251 other modules, with no missing/extra entries.
- **`python3 tools/check_aggregate.py` fails on ordering.** Recent exact
  insertions are not lexicographically sorted. `audit_architecture` compares
  coverage as sets and therefore passes; these are different checks.
  Cleanup B must sort the aggregate and test both contracts. Do not weaken
  the ordering checker or report this baseline as passing it.
- Both final `JointSoundness` and `StableHittingDomainSubEnum` dependency
  closures contain no `Eq/Internal/*`. Both still load the substantive
  UpperExpectation/UpperCoupling/UpperContinuity/UpperObservation/
  UpperQuotient/UpperRelational chain. These are not obsolete scaffolding.

No new build or kernel-verification result is claimed by this inventory.
Accepted `2dbba82` validation remains historical evidence; Cleanup B needs
its own complete verification after actual pruning.

## 2. Compatibility, facade and re-export inventory

### 2.1 Complete list of modules without substantive declarations

The scan recognizes anchored declarations, including attributed/polymorphic
ones; an import of a module named `Definition` is not a declaration.
Notation-only facades and `Check`/`Fail Check` tests require separate review.
Paths below are relative to `theories/`.

| File | Classification | Evidence and proposed action |
| --- | --- | --- |
| `PTree.v` | KEEP_FACADE | Only exports curated API/Generic and API/FreeOmega; main user entry point. |
| `API/Generic.v` | KEEP_FACADE | 66 notations exposing selected concepts/endpoints, not an old-path shim. |
| `API/FreeOmega.v` | KEEP_FACADE | 13 selected canonical-model endpoint notations, not bulk implementation exports. |
| `Semantics.v` | KEEP_FACADE | Nine curated comparison-semantics aliases; separate from canonical equality. |
| `Regression/Infrastructure/AllImports.v` | KEEP_AGGREGATE | Whole-source integration inventory; repair sorting in B. |
| `Regression/Infrastructure/ArchitectureBoundaries.v` | NEEDS_REVIEW → KEEP test | Has no theorem declarations but contains active positive and negative loading/exposure checks. Never treat as an empty shim. |

There is no confirmed `DELETE_COMPAT_SHIM` **whole file**. API/Enum,
API/SubEnum and API/Weighted also remain: they have actual user-facing
convenience definitions and must not be mistaken for alias-only modules.

### 2.2 All explicit exports, including embedded compatibility edges

| File / export | Classification and B action | Canonical owner / constraint |
| --- | --- | --- |
| `PTree.v` → API/Generic, API/FreeOmega | KEEP_FACADE | Preserve curated public surface. |
| `Eq/PEutt.v` → StableHittingRelation | DELETE_COMPAT_SHIM **edge only**, proposed | Source comment explicitly preserves the old import surface. Replace Export with Import, add explicit lower-layer imports to actual clients. Keep PEutt and every theorem. |
| `Prob/Backend/SubEnum/FreeOmega/UpperExpectation.v` → SubEnum/Expectation | DELETE_COMPAT_SHIM **edge only**, proposed | DS2.5 relocation forwarding; finite expectation belongs to native SubEnum/Expectation. Keep the raw evaluator and all its proofs. |
| `Prob/Backend/SubEnum/FreeOmega/UpperCoupling.v` → SubEnum/Expectation | DELETE_COMPAT_SHIM **edge only**, proposed | Same relocation forwarding; keep approximation/numeric coupling bridges. |
| `Prob/Backend/SubEnum/FreeOmega/UpperContinuity.v` → SubEnum/Expectation | DELETE_COMPAT_SHIM **edge only**, proposed | Same relocation forwarding; keep scalar supremum/continuity theory. |
| `Prob/Legacy/Monad.v` → Coq Rbase | NEEDS_REVIEW → retain this round | Legacy external-library export, not a renamed local owner. Removing it is unrelated to DS cleanup. |
| `Prob/Backend/Enum/Map.v`: Export EnumMap | KEEP_AGGREGATE | Exposes its own substantive nested implementation, not historical path forwarding. |
| `Prob/Backend/Enum/Coupling.v`: Export Coupling | KEEP_AGGREGATE | Same local namespace pattern; no duplicate theorem owner. |
| `Prob/Backend/Enum/IndexedCoupling.v`: Export IndexedCoupling | KEEP_AGGREGATE | Same; keep absent a demonstrated conflict. |

These four proposed edge removals alter expert unqualified import exposure,
not canonical theorem names or the curated PTree API. Their approval is
explicitly requested here. A build may reveal transitive unqualified clients:
update imports, not proof terms, and do not recreate forwarding wrappers.
Direct client counts alone cannot certify all name-resolution impacts.

### 2.3 Canonical ownership is already mostly correct

- Interface/Measure, Subprobability, AE, Coupling, Omega, Mixed retain their
  capability definitions; no class moves or capability redesign.
- Prob/FreeOmega owns generic syntax, approximation, internal observation,
  quotient and instances; no parallel Domain ownership for these objects.
- Prob/Domain owns the independent expectation/standard-measure mathematics.
- SubEnum/Expectation owns native scalar expectation facts; SubEnum/Domain
  owns the native adapter; SubEnum/FreeOmega owns its specific soundness bridge.
- Common/RealTransport and CountableRealTransport are scalar mathematics;
  Common/DomainTransport and CountableCoupling are explicitly one-way
  validation adapters. Do not bulk-export them through public facades.
- Eq/Backend/StableHittingDomainSubEnum is the PTree-to-external-model bridge.

## 3. Complete Regression inventory

`KEEP` means preserve the semantic/proof-infrastructure contract this round.
`MERGE` means move tests/fixtures to the named thematic destination and remove
the old file only after coverage and clients are preserved. It does not mean
the final theorem makes all lower-level tests redundant. No whole regression
file is proposed for unconditional `DELETE` without replacement.

All paths in the following tables are relative to `theories/Regression/`.
New destination names are proposed, not created.

### Backend (14)

| File | Decision | Reason / destination |
| --- | --- | --- |
| `Backend/BackendCapabilities.v` | KEEP | Capability resolution, especially MathComp foundational/gluing separation. |
| `Backend/CouplingRealization.v` | KEEP | Structural vs quotient/native joint contracts, empty fibers and failed independent copies; not replaced by external admissible-endpoint soundness. |
| `Backend/EnumMeasureRegression.v` | KEEP | Extensional list reorder/split laws; widely used finite-coin fixture. |
| `Backend/ExtendedEnum.v` | KEEP | Weighted/infinite-mass legacy boundary; prevents conflating Enum and subprobability. |
| `Backend/FreeOmegaEscapingMass.v` | KEEP | Counterexample to unrestricted observation/diagonal rules; fixture for Upper tests. Different from countable-matrix mass escape. |
| `Backend/FreeOmegaLimitSafety.v` | KEEP | Negative cofinality/diagonal/Fubini premise tests; not implied by one successful soundness application. |
| `Backend/FreeOmegaUpperContinuity.v` | MERGE | Into Backend/FreeOmegaUpperContracts.v; retain AE-null-branch vs everywhere-increasing distinction. |
| `Backend/FreeOmegaUpperExpectation.v` | MERGE | Same destination; retain raw nonadditivity and unreachable-test invariance. |
| `Backend/FreeOmegaUpperObservation.v` | MERGE | Same destination; retain actual RandomWalk upper mass and numerical rejection of wrong observation. |
| `Backend/FreeOmegaUpperQuotient.v` | MERGE | Same destination; retain quotient separation and rewritten RandomWalk test. |
| `Backend/NativeReflection.v` | KEEP | Countermodel with attenuated bind; native reflection needs left-unit, not an external soundness counterexample. |
| `Backend/SubEnumRegression.v` | KEEP | Reject overweight samples, retain well-formedness/finite coin fixtures and many semantic clients. |
| `Backend/UnifiedFrontierEnum.v` | KEEP | High-universe Enum/FreeOmega integration; current CI explicitly names it. |
| `Backend/UnifiedMathCompFrontier.v` | KEEP | Actual MathComp generic-profile client, not a claim of MathComp external soundness. |

### Infrastructure (19)

| File | Decision | Reason / destination |
| --- | --- | --- |
| `Infrastructure/AllImports.v` | KEEP | Integration and universe context; repair sorted order. |
| `Infrastructure/ArchitectureBoundaries.v` | KEEP | Real negative loading/exposure tests; preserve their import order. |
| `Infrastructure/CapabilityBoundaries.v` | KEEP | Checks theorems work without unused capabilities; not merely a historical signature snapshot. |
| `Infrastructure/CorrelatedInternalRounds.v` | KEEP | Quotient-vs-raw coverage and joint-round contracts; auxiliary infrastructure, not another equivalence. |
| `Infrastructure/CostedRounds.v` | KEEP | Non-unary/unbounded costs and padding; distinct internal scheduling tests. |
| `Infrastructure/CouplingReferences.v` | KEEP | No-reference counterexamples; fixture for HiddenRandomState, NativeRecovery, ResidualJointCoinduction. |
| `Infrastructure/FiniteInternalNative.v` | KEEP | SubEnum/MathComp native compression interfaces; defer deletion with its actual owner chain. |
| `Infrastructure/FiniteInternalPlan.v` | KEEP | Unbounded nonuniform costs, visible boundary and loss; fixture for three other tests. |
| `Infrastructure/FiniteInternalRound.v` | KEEP | Zero/visible/divergent round accounting; still tests maintained auxiliary code. |
| `Infrastructure/HiddenRandomState.v` | KEEP | Hidden-state hitting and rejection of zero samples; later fixtures depend on it. |
| `Infrastructure/KernelCompletion.v` | KEEP | Completion upper behavior differs from actual hitting; important negative distinction. |
| `Infrastructure/KernelCongruence.v` | KEEP | Sample exchange preserves complete hitting, exercising kernel infrastructure. |
| `Infrastructure/KernelContinuity.v` | KEEP | No uniform state cutoff; independent approximation contract. |
| `Infrastructure/NativeRecovery.v` | KEEP | Zero/partial/noninjective native recovery; not subsumed by external joint existence. |
| `Infrastructure/PairedFiniteCompression.v` | KEEP | Non-unary correlated compression and no unary realization; fixture for CorrelatedInternalRounds. |
| `Infrastructure/ResidualFinite.v` | KEEP | Unbounded retry/eventful residual examples; clients CorrelatedInternalRounds and ResidualTransport. |
| `Infrastructure/ResidualJointCoinduction.v` | KEEP | Discarded noise and always-failing/eventful retry via joint residual reasoning. |
| `Infrastructure/ResidualTransport.v` | KEEP | Candidate need not be reflexive/equivalence; protects coinduction interface. |
| `Infrastructure/UniverseSeparatedPTree.v` | KEEP | Positive/negative universe probes; not a competing public representation. |

Final soundness not depending on FiniteInternal is established by the graph;
deleting the entire maintained internal proof API is a separate liveness and
deprecation decision, not justified by that fact alone. This inventory
proposes no such deletion and no optimization of that API.

### Probability (15)

| File | Decision | Reason / destination |
| --- | --- | --- |
| `Probability/ConditionalResampling.v` | KEEP | Actual conditional resampling/retry client, not DS migration scaffolding. |
| `Probability/CorrelatedSampleAlgebra.v` | KEEP | Nonstructural probabilistic residual fixture used by strictness, exposure and fragment tests. |
| `Probability/CountableTransport.v` | MERGE | Into Probability/CountableCoupling.v; retain supplied-plan, repeated/invalid code, atomic and missing-mass cases. |
| `Probability/CountableTransportExistence.v` | MERGE | Same destination; retain existence from bidual, unequal mass, escape counterexample and infinite geometric existence. |
| `Probability/EnumDisintegration.v` | KEEP | Missing fibers, zero joint and function-state native disintegration; ConditionalResampling client. |
| `Probability/FiniteTransport.v` | KEEP | Integer/rational/subenum Hall boundary and failed Hall; different arithmetic layer from real transport. |
| `Probability/FreeOmegaDomain.v` | KEEP | Admissibility/AE/pselect/order/bind/lub contracts, especially zero-weight invalid branch. Shared basic fixtures may move, proofs stay. |
| `Probability/FreeOmegaJointDomain.v` | MERGE | Into Probability/FreeOmegaSoundness.v; retain general external joint, partial mass and large-carrier endpoints. |
| `Probability/FreeOmegaQuotientDomain.v` | MERGE | Same destination; retain actual equality FOQLComp through invalid middle, proof-choice independence and mass separation. |
| `Probability/FreeOmegaRelationalDomain.v` | MERGE | Same destination; retain genuinely heterogeneous invalid-middle derivation and countable-cover-not-validity. Move reusable geometric fixture out first. |
| `Probability/IrrationalHitting.v` | KEEP | Rational primitive schedule with irrational pi/4 limit; not ordinary geometric smoke test. |
| `Probability/OmegaVal.v` | KEEP | Pure domain algebra, non-increasing lub rejection, off-test inequality and higher universes; keep independent loading boundary. |
| `Probability/OmegaValMeasure.v` | KEEP | Countable-additive measure/integration/roundtrip and exact cemetery mass; do not merge into a file that already loaded FreeOmega. |
| `Probability/RealTransport.v` | KEEP | Irrational weights, excess capacity and empty finite carriers; pure scalar import boundary. |
| `Probability/StableHittingDomain.v` | KEEP | Automatic arbitrary-witness validity, native loss vs silent divergence, infinite visible service, noncanonical witness. |

### Semantics (21)

| File | Decision | Reason / destination |
| --- | --- | --- |
| `Semantics/AtomicInterp.v` | KEEP | Atomic preserves strictness pair; two-query handler excluded; MDPInterp fixture. |
| `Semantics/CanonicalPartialDivergence.v` | KEEP | Trace missing mass vs rejection, half-divergence vs return; current CI endpoint. |
| `Semantics/GuardedInterp.v` | KEEP | Same-handler compositionality contrast, AE-null return, heterogeneous return and real setoid rewriting. |
| `Semantics/HeadTransition.v` | KEEP | Dependent labels, terminal state, infinite service and divergent response on selected heads. |
| `Semantics/HittingDivergence.v` | MERGE | Into CanonicalPartialDivergence.v; retain SubEnum closure_spin proof (existing target also has Enum tests). No clients except aggregate. |
| `Semantics/InterpExposure.v` | KEEP | Actual TB noncongruence counterexample; shared handler fixture for Guarded/Atomic. |
| `Semantics/LabelledMDP.v` | KEEP | Nontrivial label/class probabilities and full abstraction; not covered by unlabelled reflexivity. |
| `Semantics/MDPCoincidence.v` | KEEP | Independent transition-side evidence, non-Dirac successors and MathComp profile. |
| `Semantics/MDPEmbedding.v` | KEEP | Exact encoding kernel and unlabelled collapse boundary. |
| `Semantics/MDPFragment.v` | KEEP | Decision state vs random successor distribution, infinite service; two later clients. |
| `Semantics/MDPInterp.v` | KEEP | E→F route, independent source TB, non-Dirac successors; accepted Stage 4 coverage. |
| `Semantics/OperationalPTSExamples.v` | KEEP | Finite nested/flattened hitting and observation integration; historical name alone is not deletion evidence. |
| `Semantics/PEuttAlgebra.v` | KEEP | Actual Proper/setoid/iter/interp integration; shared fixture and explicit CI endpoint. |
| `Semantics/PEuttNotation.v` | MERGE | Into PublicSemanticFacade.v; preserve both homogeneous and heterogeneous parsing, latter not currently tested there. |
| `Semantics/ProbabilisticRelationHierarchy.v` | KEEP | Stronger/behavioral separation, contextual rewrites and iteration split barriers. |
| `Semantics/PublicSemanticFacade.v` | KEEP | Curated short names, removed-pfinite negative checks and notation tests. |
| `Semantics/StableHittingComputation.v` | KEEP | Finite computation at nonuniform depths; not a pfinite equivalence. |
| `Semantics/TreeTransition.v` | KEEP | Weighted unnormalized marginal and Empty_set offered-event boundary; two clients. |
| `Semantics/TreeTransitionBisim.v` | KEEP | Action-only matching insufficient, return separation, raw recursive candidate. |
| `Semantics/TreeTransitionSoundness.v` | KEEP | Inclusion on weighted subkernel, non-equality RR, infinite interactive VN service. |
| `Semantics/TreeTransitionStrictness.v` | KEEP | 2×2 whole-continuation counterexample, fixture for four comparison/interp regressions. |

### 3.1 Merge dependency plan (avoid new cycles)

Existing fixture edges, not just similar filenames:

```text
FreeOmegaDomain → FreeOmegaQuotientDomain → FreeOmegaRelationalDomain
                                              ↓             ↓
                                    CountableTransport   CountableTransportExistence
                                              ↓
                                      FreeOmegaJointDomain
```

Arrows here mean provider → client; some direct edges are omitted. Blindly
merging the three soundness clients while CountableTransport imports their
geometric provider would create a cycle.

Proposed solution: one private `Regression/Fixtures/FreeOmegaSamples.v`
contains the existing finite coin, alternating raw term, retry, constant,
geometric definitions and only the reusable supporting proofs needed to
construct those examples. It must not import a final regression or final
joint soundness. Retain names/proofs where possible; it is not a public API.

```text
Fixtures/FreeOmegaSamples
    ├── Probability/FreeOmegaDomain
    ├── Probability/CountableCoupling
    └── Probability/FreeOmegaSoundness
```

Keep duplicate-code fixtures local to CountableCoupling unless truly shared;
move any shared ones to the same low-level fixture, not an import of a final
test. Run qualified negative import checks **before** loading fixtures which
would invalidate their intended environment. Keep pure OmegaVal/Measure and
RealTransport boundary tests in independent compilation units.

For UpperContracts, preserve the existing EscapingMass fixture and order
expectation → observation/continuity → quotient sections. No formal theory
imports Regression. Do not make Examples depend on these fixtures.

The proposal marks 58 regression files KEEP and 11 MERGE. If implemented as
specified: 11 old files become three new themed files plus one new fixture;
two merge targets already exist. Expected Regression count: **69 → 62**;
Coq module count: **252 → 245**. These are planning counts, not results or a
quota; any required extra compilation boundary must be explained in B.

## 4. Python tooling inventory (all 25 files)

Do not delete a script while a retained script still imports it or reads its
snapshot. In particular, current compiled audits import audit_capabilities,
which imports historical relocation machinery/JSON; several also reuse
audit_migration's comment scanner and frozen archive access.

| File under tools/ | Proposed B disposition | Replacement / reason |
| --- | --- | --- |
| `audit_architecture.py` | KEEP | Ownership, all-edge rules, transitive external-validation/native-expectation/internal boundaries. |
| `audit_capabilities.py` | MERGE then remove | Extract reliable coqtop query/parser to audit_assumptions; retain 25 selected contracts in audit_api. Remove historical remapping at runtime. |
| `audit_countable_transport.py` | MERGE then remove | Keep nat-existence/no-escape endpoints and whitelist checks in unified soundness/assumptions manifest; retire 245-file freeze. |
| `audit_domain.py` | MERGE then remove | Preserve expectation-domain algebra/separation contracts; no phase-specific report. |
| `audit_domain_hitting.py` | MERGE then remove | Preserve automatic admissibility and independent-kernel adequacy, not an assumed validity premise. |
| `audit_domain_joint.py` | MERGE then remove | Preserve exact qualified final signature, endpoint validity and joint/mass/support; retire 249-file freeze. |
| `audit_domain_measure.py` | MERGE then remove | Preserve sigma-additivity, integral recovery, both roundtrips and cemetery formula. |
| `audit_domain_quotient.py` | MERGE then remove | Preserve equality/sem_eq validity transport and soundness. |
| `audit_domain_relational.py` | MERGE then remove | Preserve raw cover, endpoint bidual, assumption parser and model separation; retire stage prohibition on final soundness. |
| `audit_domain_soundness.py` | MERGE then remove | Preserve admissibility, AE closure, denote approx/bind/lub; remove DS2.5 normalization dependency. |
| `audit_domain_transport.py` | MERGE then remove | Retain coding/decode and mass contracts, no supplied-plan assumption in final existence; retire 239-file freeze. |
| `audit_ds25.py` | DELETE after cutover | Completed source extraction; one-time mapping applied before writing current canonical manifest. No permanent old archive access. |
| `audit_gate_c.py` | DELETE after cutover | Historical context/import delta validator; keep final accepted signatures and capability-negative tests, not the edit history. |
| `audit_layout.py` | DELETE after cutover | Old path map/liveness report; live graph is already in architecture audit. |
| `audit_migration.py` | DELETE after cutover | Completed Gate B/Examples proof-conservation snapshots. Relocate parser utilities first; do not break importing tools. |
| `audit_prob_capabilities.py` | DELETE after cutover | 250 extracted-constant conservation snapshot is migration-specific; current declarations still build/kernel-check. |
| `audit_prob_organization.py` | DELETE after cutover | Completed exact section extraction and old-name transforms; materialize canonical names in new manifests first. |
| `audit_public_capabilities.py` | MERGE then remove | New audit_api starts with all 306 final entries, including helpers; no silent scope reduction or before/after relocation dependence. |
| `audit_real_transport.py` | MERGE then remove | Keep finite-real theorem signature, pure scalar boundary and no existence axiom; retire 243-file freeze. |
| `check_aggregate.py` | MERGE then remove | audit_architecture gains exact sorted coverage; audit_api gains optional joint-kernel runner with explicit scope. Update CI invocation first. |
| `test_audit_tools.py` | MERGE into focused tests | Keep parser errors/markers, axiom parsing, import closure, capability-negative and scope completeness tests; discard historical edit-delta fixtures only. |
| `test_countable_transport.py` | MERGE into test_soundness | Retain negative assumption/dependency tests; remove frozen revision comparisons. |
| `test_domain_joint.py` | MERGE into test_soundness | Keep new-axiom/capability, endpoint signature and one-way validation mutations. |
| `test_domain_transport.py` | MERGE into test_soundness | Keep no assumed existence/domain separation tests; retire pre-existence stage prohibition. |
| `test_real_transport.py` | MERGE into test_soundness | Keep scalar isolation and assumption mutations; retire old-file byte equality. |

Target: four audit entry points (`audit_architecture`, `audit_api`,
`audit_assumptions`, `audit_soundness`) and focused tests. Shared parser/query
functions may live in audit_assumptions; no new hierarchy of stage wrappers.
Exact final Python count is decided by that split, not a deletion quota.

### 4.1 Safety coverage that must precede retiring old audits

| Safety property | Existing evidence | Required stable replacement |
| --- | --- | --- |
| Unfinished proofs rejected | CI grep + per-stage source guards | Comment-aware all-maintained-source scan; catch Admitted and tactic admit, not only a line beginning `admit.`. |
| No new semantic axioms/capabilities | Stage ban on Axiom/Parameter/Class + compiled types/assumptions | Explicit declaration/axiom allowlist and diff policy; negative mutation adds a local axiom/class and must fail. Existing legitimate Interface classes are not banned. |
| Domain independent of syntax | architecture + per-stage checks + Fail Check | Preserve live direct and transitive rules and pure-module negative compilation tests. |
| Mainline independent of validation | architecture transitive closure | Same roots/rules, including indirect native-backend leakage; no facade helper additions. |
| Correct final joint contract | compiled Check @ + Print Assumptions | Exact qualified endpoint manifest: arbitrary A/B/T, SubEnum, two admissibility premises, oval_coupled conclusion, no supplied joint/capability. Signature drift fails. |
| Hitting validity not assumed | DS4 compiled checks | Exact automatic-validity/adequacy signatures and source kernel separation. |
| Public/capability stability | 306 + 25 current contracts | Canonical current-name manifest, full types and per-endpoint logical dependencies. Keep existing scope initially. |
| Parser fails safely | test_audit_tools | Nonzero exit OR Coq Error, missing/duplicate markers, unparsed assumptions and missing endpoint all fail. |
| Aggregate and kernel checking | check_aggregate + CI | Sorted exactly-once inventory AND qualified boundary tests; explicit distinction between targeted recursive and full-library checks. |

Minimum final soundness manifest includes (with their canonical owners):

- Domain/Expectation: `oval_lub`, bind continuity/diagonal endpoints.
- Domain/MeasureModel: `oval_integral_recovery`, `oval_probability_roundtrip`,
  `probability_oval_roundtrip`, `oval_probability_bottom`; retain the compiled
  sigma-additivity/measure construction endpoints from DS1b as well.
- SubEnum/FreeOmega/DomainSoundness: `free_omega_denote_approx`,
  `free_omega_denote_bind`, `free_omega_denote_lub`.
- SubEnum/FreeOmega/QuotientSoundness: `free_omega_qlift_eq_sound`,
  `free_omega_sem_eq_sound`, and their admissibility transport endpoints.
- Eq/Backend/StableHittingDomainSubEnum:
  `stable_hitting_admissible`, `stable_hitting_denotational_adequacy`.
- Common/DomainTransport: `oval_bidual_coupled_nat`.
- Common/CountableCoupling: `oval_bidual_coupled`, `oval_countable_coupling_iff`.
- SubEnum/FreeOmega/JointSoundness: `free_omega_qlift_sound`,
  `free_omega_qlift_eq_sound_via_joint`, `free_omega_qlift_joint_mass_support`.

Do not use just a name search or shared broad axiom whitelist as the new
signature audit. Preserve full compiled types and per-endpoint assumption
sets. Old reports must be compared against the new manifest **before** they
are removed. Any selected-scope reduction needs a written coverage mapping.

## 5. Documentation inventory (all 44 existing files)

MERGE means preserve the useful content in a stable destination, then remove
the stage file and update inbound links. DELETE means historical evidence
already lives in git; it is conditional on removing all runtime consumers.

| File under docs/ | Decision | Destination / reason |
| --- | --- | --- |
| `ARCHITECTURE_AUDIT.md` | KEEP | Live generated ownership/client inventory, linked from ARCHITECTURE.md. |
| `ARCHITECTURE_BASELINE.md` | DELETE | Historical pre-migration inventory; git retains it. |
| `ARCHITECTURE_CLEANUP.md` | MERGE | ARCHITECTURE.md: roles/direction, omit gate chronology. |
| `ARCHITECTURE_MIGRATION.md` | MERGE | ARCHITECTURE.md: final mixed-responsibility split, not migration recipes. |
| `CAPABILITY_BASELINE.md` | DELETE after manifest cutover | Historical 25-entry comparison base currently read by audit_capabilities. |
| `CAPABILITY_CURRENT.md` | MERGE | Stable generated API/assumptions report, no relocation history. |
| `CAPABILITY_GATE_C_AFTER.json` | MERGE | Current canonical API manifest; preserve all 306 entries initially. |
| `CAPABILITY_GATE_C_BEFORE.json` | DELETE after cutover | Reviewed historical delta only. |
| `CAPABILITY_PUBLIC_INDEX.md` | MERGE | Generated API index from new canonical manifest. |
| `CAPABILITY_REVIEW.md` | MERGE | ARCHITECTURE.md/API notes: real capability boundaries, not cleanup transcript. |
| `DOMAIN_COUNTABLE_TRANSPORT.md` | MERGE | FREEOMEGA_SOUNDNESS.md: tail-lumped cuts, tightness/no mass escape. |
| `DOMAIN_COUNTABLE_TRANSPORT_AUDIT.md` | MERGE | Stable assumptions manifest/report: nat existence and matrix contracts. |
| `DOMAIN_DS1A.md` | MERGE | FREEOMEGA_SOUNDNESS.md: bounded observational domain, order and continuity. |
| `DOMAIN_DS1A_AUDIT.md` | MERGE | Stable assumptions manifest/report: independent-domain endpoints. |
| `DOMAIN_DS1B.md` | MERGE | FREEOMEGA_SOUNDNESS.md: discrete lifted-carrier measure correspondence. |
| `DOMAIN_DS1B_AUDIT.md` | MERGE | Stable assumptions manifest/report: sigma-additivity, recovery and roundtrips. |
| `DOMAIN_DS2.md` | MERGE | FREEOMEGA_SOUNDNESS.md: admissibility, AE/pselect, algebra interpretation. |
| `DOMAIN_DS25.md` | MERGE | ARCHITECTURE.md: native finite expectation precedes FreeOmega validation. |
| `DOMAIN_DS25_BEFORE.json` | DELETE after cutover | Extraction snapshot; remove audit_ds25/normalization consumers first. |
| `DOMAIN_DS2_AUDIT.md` | MERGE | Stable assumptions manifest/report: qualified denotation endpoints. |
| `DOMAIN_DS3.md` | MERGE | FREEOMEGA_SOUNDNESS.md: all-raw equality bridge, invalid intermediate allowed. |
| `DOMAIN_DS3_AUDIT.md` | MERGE | Stable assumptions manifest/report: equality/sem_eq contracts. |
| `DOMAIN_DS4.md` | MERGE | FREEOMEGA_SOUNDNESS.md: independent finite kernel, hitting adequacy and native loss. |
| `DOMAIN_DS4_AUDIT.md` | MERGE | Stable assumptions manifest/report: automatic validity, arbitrary witnesses. |
| `DOMAIN_DS5A_FOUNDATIONS.md` | MERGE | FREEOMEGA_SOUNDNESS.md: raw enumerable cover and bidual, not validity by countability. |
| `DOMAIN_DS5A_FOUNDATIONS_AUDIT.md` | MERGE | Stable assumptions manifest/report: retained support/dual bridge endpoints. |
| `DOMAIN_JOINT_SOUNDNESS.md` | MERGE | FREEOMEGA_SOUNDNESS.md: final scoped theorem, decode and equality alignment. |
| `DOMAIN_JOINT_SOUNDNESS_AUDIT.md` | MERGE | Stable assumptions manifest/report: final exact signature, mass and support. |
| `DOMAIN_REAL_TRANSPORT.md` | MERGE | FREEOMEGA_SOUNDNESS.md: finite Hall, rounding, compactness, actual mass. |
| `DOMAIN_REAL_TRANSPORT_AUDIT.md` | MERGE | Stable assumptions manifest/report: finite-real foundation. |
| `DOMAIN_TRANSPORT_PREPARATION.md` | MERGE | FREEOMEGA_SOUNDNESS.md: atomic representation and code/decode; remove obsolete OPEN claim. |
| `DOMAIN_TRANSPORT_PREPARATION_AUDIT.md` | MERGE | Stable assumptions manifest/report: necessary coded-marginal contracts. |
| `EXAMPLES_FOLLOWUP.md` | MERGE | ARCHITECTURE.md: Examples vs Regression, standard ITree effects, private internal machinery. |
| `FREEOMEGA_DOMAIN_SOUNDNESS.md` | MERGE | FREEOMEGA_SOUNDNESS.md: final conclusions/boundaries, not future-tense design plan. |
| `INTERP_COMPOSITIONALITY.md` | KEEP | Distinct maintained mathematical story; update any dead links, do not rewrite Stage 1–4 theory. |
| `LAYOUT_AUDIT.md` | DELETE | Historical path/client snapshot; current architecture report replaces it. |
| `LAYOUT_VALIDATION.md` | DELETE | Historical local verification record; git retains it, not current CI evidence. |
| `PROB_CAPABILITY_BEFORE.json` | DELETE after cutover | 250 extracted-declaration migration snapshot, not public API. |
| `PROB_ORGANIZATION.md` | MERGE | ARCHITECTURE.md: native axis and generic FreeOmega separation. |
| `UNIVERSE_CONSISTENCY.md` | KEEP | Enduring explanation of universe constraints and joint checking; not mere rename history. |
| `examples-moves.json` | DELETE after cutover | Only historical migration map; no current audit may depend on it afterwards. |
| `gate-b-moves.json` | DELETE after cutover | Same; current compiled query still loads it today. |
| `module-moves.tsv` | DELETE after cutover | Old layout translation for retired tooling. |
| `prob-organization.json` | DELETE after cutover | Section extraction/rename manifest; resolve names before retiring consumers. |

Two principal narrative documents are proposed: ARCHITECTURE.md and
FREEOMEGA_SOUNDNESS.md. Keep generated architecture/API/assumption reports
and a canonical machine-readable contract manifest separately; generated
contract text is evidence, not another phase narrative. Retain the focused
Interp and universe explanations. README and workflow links must be updated
in B; there are no link changes in A.

The final soundness document must explicitly preserve these distinctions:

1. Raw FreeOmega is syntax; only admissible endpoints denote probabilities.
2. OmegaVal equality is bounded-test equality, not record equality.
3. DS1b models discrete lifted carriers; not arbitrary measurable-space representation.
4. Missing mass includes native sampling loss as well as internal divergence;
   an infinite visible service need not lose current stable-hitting mass.
5. General relational qlift soundness is SubEnum-qualified, not completeness.
6. Raw/inadmissible FOQLComp intermediates remain allowed.
7. No MathComp-native external soundness is claimed.

## 6. Proposed final shape and B execution order

```text
theories/                         formal owners unchanged
  API/, Core/, Eq/, Interp/, Semantics/
  Prob/{Interface,FreeOmega,Domain,Backend,Legacy}/
  Examples/
  Regression/
    Fixtures/FreeOmegaSamples.v   private, one-way reusable data/proofs
    Backend/FreeOmegaUpperContracts.v
    Probability/FreeOmegaDomain.v
    Probability/FreeOmegaSoundness.v
    Probability/CountableCoupling.v
    ...                          KEEP contracts in the inventory
tools/
  audit_architecture.py
  audit_api.py
  audit_assumptions.py
  audit_soundness.py
  test_*.py                      focused long-term mutation/parser tests
docs/
  ARCHITECTURE.md
  FREEOMEGA_SOUNDNESS.md
  ARCHITECTURE_AUDIT.md
  ...                            current generated contracts + focused docs
```

After A is accepted, B should proceed in dependency order:

1. Capture current canonical compiled contracts and map every retained
   long-term assertion to the new audit; demonstrate old/new overlap equality.
2. Implement stable audits/tests without old commit IDs or relocation JSON
   runtime dependencies. Preserve negative mutation tests before removing
   phase scripts and byte-for-byte freeze checks.
3. Remove the four approved compatibility export edges; update actual
   imports only. Preserve fully qualified endpoints and curated API.
4. Extract the shared fixture, merge the 11 proposed regression files, retain
   all named boundaries below. No theory or proof-structure redesign.
5. Consolidate docs/reports; remove retired files only after runtime imports,
   CI commands and README/doc links have been updated.
6. Regenerate sorted AllImports and architecture inventory; run full build,
   stable assumptions/API/soundness audits and joint kernel checks.
7. Report actual before/after counts, proof/API conservation, all deletions,
   and verification scope. Deleted tracked material is recoverable from git.
   Pause for acceptance; do not start MathComp soundness or new theory.

### B acceptance witnesses that must remain machine checked

| Boundary | Current witness to retain (relocation allowed) |
| --- | --- |
| Invalid raw FreeOmega exists | FreeOmegaDomain.alternating_bool_not_admissible |
| Raw qlift does not imply validity | FreeOmegaJointDomain.qlift_alone_still_not_admissible |
| Actual invalid middle, not just equivalent endpoints | FreeOmegaRelationalDomain.heterogeneous_invalid_middle + FreeOmegaJointDomain.heterogeneous_joint_through_invalid; equality_through_invalid_middle as well |
| AE zero branch differs from positive invalid branch | FreeOmegaDomain.null_weight_bad_branch_admissible and positive_bad_branch_not_admissible |
| Countable mass escape is rejected | CountableTransportExistence.escaping_row_still_has_mass, escaping_pointwise_zero, escaping_fails_no_escape_bound |
| Invalid/repeated codes do not leak mass | CountableTransport.invalid_code_not_supported, duplicate_codes_not_injective, decode_preserves_missing_mass; FreeOmegaJointDomain.duplicate_invalid_codes_joint |
| Partial mass remains partial | OmegaValMeasure.half_mass_at_bottom/half_mass_at_true; FreeOmegaJointDomain.partial_joint_keeps_mass_and_support with existing half-mass endpoints |
| Infinite support genuinely uses existence theorem | CountableTransportExistence.geometric_successor_joint_exists, not only a supplied plan |
| Large carriers | FreeOmegaJointDomain.type_carrier_joint and type_valued_qlift_joint; UniverseSeparatedPTree probes |
| Equality aligns with DS3 | FreeOmegaJointDomain.equality_joint_recovers_ds3 |
| Hitting missing mass is not only divergence | StableHittingDomain.silent_hitting_bottom, native_loss_hitting_bottom, infinite_visible_service_mass_one |
| Irrational limit from rational primitives | IrrationalHitting.pi_canonical_hitting_mass and pi_canonical_hitting_irrational |
| Whole continuation matters | TreeTransitionStrictness.peutt_strictly_contained_in_tree_trans_bisim + InterpExposure counterexample |

No blanket reduction to one large regression file: pure import-boundary tests,
universe tests, finite-real arithmetic and standard measure correspondence
justify separate compilation units.

## 7. Stop point

Cleanup A changes only this inventory. No theory, Regression, tool, workflow,
AllImports, existing report or proof has been modified. Cleanup B is blocked
on user acceptance of these dispositions, especially the four export-edge
removals and the thematic merge/fixture plan.

This inventory is itself temporary acceptance material: after the approved
B changes and disposition accounting are recorded, it can be retired into
git history rather than becoming another permanent architecture narrative.

Inventory coverage was checked against `git ls-tree -r --name-only 2dbba82`:
all 69 regression, 25 tooling and 44 documentation paths appear exactly once
in their respective tables. The 58 KEEP / 11 MERGE totals and subgroup counts
were computed from the table rows, not inferred from the proposed end state.
