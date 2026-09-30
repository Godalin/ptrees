# FreeOmega: generic external soundness

FreeOmega has a **native-parametric external validation into OmegaVal**.
A backend supplies `native : forall X, MN X -> OmegaVal R X` and proves
compatibility with its native operations. Modelable FreeOmega terms then have
genuine subprobability semantics. Moreover, **every complete PTree stable-hitting
witness is automatically modelable**, for both SubEnumQ and SubEnumR.

The entry point is `Prob/FreeOmega/Validation/Soundness.v`. It reexports existing
results; it does not add a second free syntax, probability interface, or an
actual-joint-existence assumption. Maintained PTree reasoning never imports
external validation. See [architecture](ARCHITECTURE.md).

## 1. Generic external model

`Prob/FreeOmega/Validation/Model.v` owns the canonical validation vocabulary:

```coq
free_omega_model_upper native t
free_omega_modelable native t
free_omega_model Ht
free_omega_model_denotes native t L
```

The model packages the existing evaluator with its probability-functional laws;
there is no second recursive interpretation. `Model.v` imports neither concrete
native backends nor PTree. `Soundness.v` additionally exposes the separate
PTree-facing `StableHitting.v` bridge.

### Independent mathematical domain

`Prob/Domain/Expectation.v` defines `OmegaVal R A`: an evaluator
`(A -> R) -> R` satisfying zero, monotonicity, bounded scaling/additivity,
mass at most one, and monotone continuity on `[0,1]`-valued tests. It is not
inductive syntax or a second free completion. Direct mathematical operations are

```text
bottom(f)   = 0
ret x(f)    = f(x)
bind L k(f) = L(fun x => k(x)(f))
lub c(f)    = sup_n c(n)(f), provided c is increasing
```

Order and equality compare all bounded tests, not literal record equality
or arbitrary unbounded evaluators. The pointed omega-CPO laws, bind continuity
on both sides, and diagonal cofinality are proved here. An arbitrary sequence
cannot be passed to `oval_lub` without an increasingness proof.

`Prob/Domain/MeasureModel.v` anchors this domain in MathComp measure theory.
Indicators define a countably additive subprobability measure; countable
additivity follows from increasing finite unions and evaluator continuity.
Simple-function approximation and monotone convergence prove
`oval_integral_recovery`. Conversely bounded integration defines an OmegaVal.
Adding a cemetery point gives an actual probability measure on the **discrete
lifted carrier `A + {bottom}`**, with bottom mass exactly `1 - oval_mass L`.
`oval_probability_roundtrip` and `probability_oval_roundtrip` prove both
directions of correspondence. This is not a representation theorem on arbitrary
measurable spaces; the HB adapter has its ordinary carrier-universe scope.
OmegaVal itself and the later coupling bridge support larger carriers.

## 2. Modelability and denotation

FreeOmega remains permissive syntax: FORet, FOZero, FOSample and raw FOLub.
A Lub alternating between distinct Dirac values is generally nonadditive.
Therefore **raw syntax alone, or reflexive qlift, is not a validity certificate**.

`modelable_iff_denotes` characterizes modelability by existence of an OmegaVal
interpretation. Ret/zero, valid sampling/bind, and increasing modelable Lubs are
closed. The AE variants `modelable_sample_ae` and `modelable_bind_ae` permit
invalid terms on null branches; they do not require everywhere validity.
`model_denotes_bind` and `model_denotes_lub` give the algebraic interpretation.
`Iteration.v` connects FreeOmega Kleisli iteration to the mathematical omega-limit
and least-fixed-point construction.

## 3. Quotient and relational soundness

The generic chain is `Continuity → Observation → Relational → Quotient`.
The backend discharges six explicit obligations: AE concentration and preservation
of ret, zero, bind, relational bounded-test inequalities, and **existing native
lub witnesses**. It is not required to be native omega-complete.
See [the exact obligations](GENERIC_QLIFT_VALIDATION.md).

`model_qlift_bidual_raw` gives bounded-test constraints for all raw qlift
derivations. `model_qlift_bidual` interprets modelable endpoints. Equality gives
`model_qlift_eq_modelable` and `model_qlift_eq_sound` (observational `oval_eq`).
FOQLComp may pass through an inadmissible middle term: the proof of the raw
constraints never requires a probability model for it. No later hitting or
joint bridge re-inducts on qlift. Generic bidual soundness is **not** a generic
actual-joint existence theorem.

## 4. Generic stable-hitting modelability

`Prob/FreeOmega/Validation/StableHitting.v` defines an independent mathematical
primitive kernel. Ret/Vis give stable Dirac heads, Tau an internal Dirac state,
and Prob a bind of the native interpretation with internal successors.
`ptree_model_approx` iterates this mathematical kernel, and
`ptree_model_hitting` is its increasing OmegaVal lub.

The proof has two distinct dependency levels:

1. `ptree_hitting_model_commutation` identifies finite formal approximants with
   these mathematical values. They are modelable and increasing, hence
   `ptree_canonical_hitting_modelable` proves validity of their formal FOLub.
   This part only needs the native interpretation, not the six compatibility
   obligations.
2. An arbitrary complete witness is quotient-equal to the canonical frontier.
   The six obligations above let existing generic qlift equality soundness
   transport validity and denotation to that witness.

```text
stable_hitting_modelable:
  ptree_stable_hitting s out -> free_omega_modelable native out

stable_hitting_denotational_adequacy:
  ptree_stable_hitting s out ->
  free_omega_model_denotes native out (ptree_model_hitting native s)

stable_hitting_model_mass_lub:
  mass(denote out) = sup_n mass(ptree_model_approx native n s)
```

These are schematic statements with the canonical observable FreeOmega profile
understood. Validity is a conclusion, never a caller-supplied premise. There is
no AST, no-event, finite-support-of-the-limit, or total-native-mass requirement.
The fuel convention sees a current Ret/Vis at zero; Tau/Prob consumes fuel.

Missing mass includes native subprobability loss **and** failure to reach the
next stable head. It is not unconditionally divergence probability. Infinite
visible interaction may have next-head mass one without terminating. Visible
heads preserve their whole continuation; this is not an infinite-path measure.

## 5. SubEnumQ specialization and compatibility boundary

`SubEnumQ/Domain.v` interprets finite rational subdistributions independently of
FreeOmega. `SubEnumQ/FreeOmega/Validation.v` supplies the native compatibility
proofs and instantiates generic quotient validation. Pure scalar native-limit
lemmas live in `SubEnumQ/NativeLimit.v`, not in a formal FreeOmega observation
module. The canonical adapter does not depend on the specialized upper chain.

`Eq/Backend/StableHittingDomainSubEnumQ.v` specializes the generic hitting proof:
`subenumQ_stable_hitting_modelable` and
`subenumQ_stable_hitting_denotational_adequacy` are the preferred endpoints.
Existing `stable_hitting_admissible` / `ptree_domain_hitting` clients are retained;
their core commutation and validity proofs now delegate to the generic theorem.

**Legacy external API:** `Compatibility.v` now owns the old
`free_omega_admissible`, `free_omega_domain`, equality and joint-soundness names.
Their validation proofs delegate to generic Model/quotient validation and the
canonical Q realization. `Admissibility.v`, `DomainSoundness.v`,
`QuotientSoundness.v` and `CouplingSoundness.v` have been removed; remaining
legacy clients import `Compatibility` explicitly. This preserves their theorem
statements, not their former module paths. New code should use `free_omega_model`
and the `subenumQ_*` endpoints. Both Q/R canonical countable-support and joint
paths transitively exclude this compatibility API and the old scalar upper
chain; an import-boundary regression checks the Q client directly.

The compiled migration preserves all 491 recorded theorem types (modulo the
explicit owner relocation). Nineteen legacy compatibility endpoints lose the
`Eqdep.Eq_rect_eq.eq_rect_eq` dependency when delegated to generic proofs;
the runner's `runner_stable_hitting_adequacy` also loses that dependency.
Their snapshots record exactly these removals, not an expanded axiom whitelist.
Ret/zero closure uses the domain laws directly, without importing assumptions
from an unused native interpretation. This is not an axiom-freedom claim.

**Scalar native mathematics is different:** `UpperExpectation`, `UpperCoupling`,
`UpperContinuity`, `UpperRelational`, `UpperQuotient` and related files still
support native transport/reflection and internal joint witnesses (including
`NativeTransport` and EnumQ upper observation). They are not merely obsolete
external validation. Replacing these proofs with OmegaVal imports would make
maintained reasoning depend on its external model. They remain on the safe,
non-validation side of that boundary; this cleanup does not redesign them.

## 6. SubEnumR specialization

`SubEnumR/Domain.v` interprets finite real subdistributions.
`SubEnumR/FreeOmega/Validation.v` collects its compatibility proofs and quotient
specializations; it neither converts through rationals nor copies FreeOmega
proofs. `Eq/Backend/StableHittingDomainSubEnumR.v` now provides:

```text
subenumR_stable_hitting_modelable
subenumR_stable_hitting_denotational_adequacy
subenumR_stable_hitting_domain_eq
subenumR_stable_hitting_mass_lub
```

For **any event signature, return type, tree and complete witness**, these
endpoints discharge all native obligations. Regression covers arbitrary
witnesses, recursive real-weight sampling followed by visible interaction,
zero native mass, and a noncanonical Dirac witness. The recursive test permits
success probability zero: validity is not a termination assertion.

## 7. Optional backend-specific actual joint realization

`SubEnumQ/FreeOmega/JointRealization.v` and
`SubEnumR/FreeOmega/JointRealization.v` keep the stronger results outside generic
validation. The preferred `subenumQ_qlift_sound` / `subenumR_qlift_sound` accept
modelable endpoints and conclude `oval_coupled` for their generic models.
The old rational `free_omega_qlift_sound` remains as a compatibility endpoint.

Both proofs compose endpoint countable support, generic bidual soundness, and
`Common/CountableCoupling.v`'s actual transport existence theorem. The resulting
joint has exact bounded-test marginals and relation concentration; its mass is
the common marginal mass, without normalization.

The independent transport proof is:

1. Every raw FreeOmega term has an enumerable cover, possibly with duplicates
   and invalid codes. Admissibility gives concentration of its OmegaVal value.
2. The existing all-raw qlift bounded-test bridge gives bidual inequalities,
   equal actual mass and setwise Hall inequalities. Only endpoints are valid.
3. Countable concentration reduces arbitrary carriers to nat-coded marginals;
   the relation restricts to valid codes. No decidable equality, inhabitedness,
   countability of the entire carrier or decidable relation is assumed.
4. `Common/RealTransport.v` proves finite real Hall transport by integer
   matching, floor/ceiling rounding and finite compactness. Equal mass upgrades
   subtransport to exact two-sided marginals.
5. `Common/CountableRealTransport.v` uses tail-lumped finite windows and product
   compactness. Crucially every row prefix satisfies
   `p_i - tail_q(m) <= sum_(j<m) w_ij <= p_i` (and symmetrically for columns).
   Vanishing tails prevent mass escaping to infinity. Coordinatewise compactness
   alone would be insufficient: `w_n(0,n)=1` converges coordinatewise to zero.
6. `Domain/Matrix.v` sums unnormalized rows to realize the joint; no division
   by zero-mass rows is needed. `Common/DomainTransport.v` proves
   `oval_bidual_coupled_nat`; `Common/CountableCoupling.v` decodes the joint
   back to the original carriers. Invalid codes carry no positive mass.

External bidual/joint equivalence is established for countably supported
OmegaVal margins. It is **not** completeness of syntactic qlift. The final
FreeOmega bridge composes these results without inspecting FOQLComp.

## Regression and verification map

| Contract | Maintained regression |
| --- | --- |
| Independent domain, increasing Lub, bounded equality, universe | `Probability/OmegaVal` |
| Countable measure, integrals, missing mass, roundtrips | `Probability/OmegaValMeasure` |
| Raw nonadditivity, native AE, upper/observation/quotient laws | `Probability/FreeOmegaUpperContracts` |
| Invalid raw terms and admissible construction | `Probability/FreeOmegaDomain` |
| Countable coding, explicit plans, actual existence, no escape | `Probability/CountableCoupling` |
| FOQLComp through invalid middle, equality, general joint, high universe | `Probability/FreeOmegaSoundness` |
| Finite real irrational weights / Hall | `Probability/RealTransport` |
| Generic model/quotient validation and Q/R adapters | `Probability/GenericFreeOmegaValidation`, `Probability/GenericQuotientValidation` |
| Arbitrary Q/R hitting witnesses, partial mass, infinite service | `Probability/StableHittingDomain` |
| Rational coins / irrational limiting mass | `Probability/IrrationalHitting` |

Paths are under `theories/Regression`. The private shared sample fixture is
not a new public API. Raw observation escaping mass and countable matrix mass
escape remain different negative tests. `FreeOmegaLimitSafety` retains the
negative continuity/diagonal/Fubini tests; formal FiniteInternal/Recovery
infrastructure is not deleted by this validation result.

Existing compiled types are mechanically namespace-relocated, not reset.
Six old Q hitting contracts (`ptree_domain_hitting_of_denotes`,
`ptree_domain_hitting_zero`, `stable_hitting_admissible`,
`stable_hitting_denotational_adequacy`, `stable_hitting_domain_eq`, and
`stable_hitting_mass_lub`) keep exactly their types but lose the old
`eq_rect_eq` dependency through generic proof reuse. Only that confirmed
assumption reduction is recorded; no axiom is added or whitelist widened.
`audit_soundness.py --stable-hitting-only` additionally checks generic
hitting, Q/R specialization and regression endpoints against the existing
logical-axiom whitelist. Architecture checks enforce one-way validation and
reject legacy completion/tree dependencies in the native adapters.

```sh
opam exec -- dune build
python3 tools/audit_architecture.py --check
python3 tools/audit_soundness.py --source-only
python3 tools/audit_soundness.py --stable-hitting-only
python3 tools/audit_soundness.py --generic-quotient-only
python3 tools/audit_contracts.py
python3 -m unittest discover -s tools -p 'test_*.py'
```

Not established: arbitrary invalid-term denotation, syntactic coupling
completeness, arbitrary-backend joint existence, MathComp-native external
soundness, infinite path measures, or a whole-library kernel audit. Local
verification does not assert remote CI success.

### Compatibility cleanup: local verification

- Complete `dune build`, including AllImports and extraction targets: passed.
  The inventory is 434 modules (four retired in this cleanup), including the unchanged two Gate M modules;
  the new validation code is entirely Gate S.
- Architecture, API surface and source-soundness audits: passed.
- 148 Python tool tests: passed, including transitive canonical-realization
  isolation and rejection of a duplicated model construction in Compatibility.
- Exact compiled contract suites: `contracts` 491 and `runner_distribution` 28
  entries passed after the explicit owner relocations and the nineteen-plus-one
  `eq_rect_eq` dependency removals documented above. Types and all other
  assumptions are unchanged; snapshots were not broadly regenerated.
- Compiled soundness audits: 32 hitting/Q/R/realization endpoints and 45 generic
  quotient/adapter/regression endpoints passed the unchanged axiom whitelist.
- Joint `coqchk -norec`: six module bodies passed—Q Validation/CountableSupport/
  JointRealization/Compatibility, the Q hitting specialization, and the
  GenericFreeOmegaValidation regression. Compiled
  dependencies were trusted; this is not a recursive whole-library audit.
- No CI or environment change was performed. Scalar native Upper infrastructure
  and the combined Soundness entry point remain intentionally unchanged, apart
  from correcting the former's role comment.
