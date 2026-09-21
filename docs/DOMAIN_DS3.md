# DS3: quotient equality soundness

Baseline: **DS2.5 accepted at `7a3bf82`**. This stage adds four theorems in
`Prob/Backend/SubEnum/FreeOmega/QuotientSoundness.v`, then stops for review.
DS4 stable-hitting adequacy and general relational coupling realization
are not part of this stage.

## The mathematical route

```text
free_omega_qlift eq t u
          │ existing free_omega_qlift_eq_upper, valid for ALL raw terms
          ▼
upper(t,f) = upper(u,f) for every [0,1]-valued test f
          ├──> admissible t ↔ admissible u
          └──> oval_eq (domain Ht) (domain Hu)
```

The first new implication uses DS2's `free_omega_admissible_ext`, i.e.
bounded-test equality transports the evaluator laws. The second simply
packages the same evaluator equality. No induction on `free_omega_qlift`
is performed in DS3; no intermediate validity obligation is added to its
composition constructor. No new evaluator, representation or axiom is used.

The four maintained external-validation endpoints are:

```coq
free_omega_qlift_eq_admissible :
  free_omega_qlift eq t u ->
  (free_omega_admissible R t <-> free_omega_admissible R u).

free_omega_qlift_eq_sound :
  forall (Ht : free_omega_admissible R t)
         (Hu : free_omega_admissible R u),
  free_omega_qlift eq t u ->
  oval_eq (free_omega_domain Ht) (free_omega_domain Hu).

free_omega_sem_eq_admissible :
  sem_eq t u ->
  (free_omega_admissible R t <-> free_omega_admissible R u).

free_omega_sem_eq_sound :
  forall (Ht : free_omega_admissible R t)
         (Hu : free_omega_admissible R u),
  sem_eq t u ->
  oval_eq (free_omega_domain Ht) (free_omega_domain Hu).
```

These displayed signatures omit carrier binders only: `R : realType` and
`t,u : FreeOmega SubEnum A`. In the actual declarations, `sem_eq` explicitly
uses `FreeOmegaObservableSemanticMeasure` with the concrete SubEnum
measure/omega instances. It is **not** the auxiliary structural equality.
The raw qlift definition, both measure instances and admissibility are
unchanged. There is no generic `Semantic*` capability premise.

Although the soundness endpoints accept validity proofs for both terms,
only one endpoint needs to be independently known valid: the preceding iff
constructs the other proof. The conclusion accepts **any** such proofs and
is observational `oval_eq`, not equality of law records or raw terms.

## Why the intermediate-term caveat matters

The new `Regression/Probability/FreeOmegaQuotientDomain.v` constructs:

```text
FOLub (const (FORet tt)) -- universal unit/bool relation --> alternating_bool
alternating_bool       -- universal bool/unit relation --> FORet tt
```

An explicit `FOQLComp` with `mid := alternating_bool` composes these into
equality on the unit carrier. DS2 already proves that this Boolean
alternating raw Lub is **not admissible**. Nevertheless DS3 transports
validity between the endpoints and proves their `oval_eq`.

Thus requiring every intermediate raw term to be admissible would really
be too strong, not merely inconvenient. The proof uses actual quotient
composition evidence, rather than replacing it with reflexivity. This
does not interpret the bad middle term as a probability measure.

Other checked boundaries:

- an inadmissible raw term is still qlift-equal to itself; equality alone
  does not establish validity;
- an inadmissible term cannot be observable-sem-equal to a valid term;
- an unbounded retry Lub is sem-equal to its constant outer Lub, and the
  new endpoints transport validity and validate the equality;
- arbitrary supplied validity proofs yield the same soundness conclusion;
- zero cannot be sem-equal to a returned unit: quotient equality cannot
  erase missing mass;
- importing the new validation theory loads neither PTree/peutt nor the
  MathComp measure adapter. DS1b provides that independent anchor already.

## Scope and isolation

This is **SubEnum-qualified equality soundness**. It is not completeness,
not unconditional admissibility of raw FOLub, not general `qlift S` joint
coupling realization, and not a MathComp-native backend theorem.

The new module is classified as external validation. No API, Eq, Interp,
example or ordinary probability module imports it. The existing transitive
architecture checks enforce this separation. Native expectation/domain
remain independent of FreeOmega.

`audit_domain_quotient.py --source` compares all 229 baseline `.v` files
byte-for-byte with `7a3bf82`, permitting only the two exact AllImports
insertions. Only the new theory and regression files are added. This
protects DS1, DS2, DS2.5 and all maintained FreeOmega reasoning infrastructure.
Historical source audits keep their frozen scope; they are not weakened
to accept new stages. The prior compiled snapshots are also not rewritten.

The DS3 compiled audit checks all four core endpoints, the two pre-existing
bridges and thirteen regression/helper endpoints (19 in total), including
`Print Assumptions`. Its whitelist is exactly DS2's whitelist, and it checks
the explicit validity boundary and observable instance. Negative tooling
tests cover unexpected source changes, missing validity, a wrong equality
instance, added axioms and failure to restore the shared query scope.

## Verification

All of the following completed successfully locally:

- `opam exec -- dune build`, including AllImports;
- `python3 tools/check_aggregate.py`: 230 imported modules;
- `python3 tools/audit_architecture.py --check`: external-model isolation
  and native-domain/FreeOmega separation still hold transitively;
- `python3 tools/audit_domain_quotient.py --check`: exact source isolation
  plus the [19-entry compiled type/assumption snapshot](DOMAIN_DS3_AUDIT.md);
- DS1a, DS1b and DS2 compiled audits (`audit_domain.py`,
  `audit_domain_measure.py`, `audit_domain_soundness.py`, all with `--check`):
  the 37/37/51-entry snapshots remain unchanged;
- DS2.5's historical exact source audit replayed against frozen `7a3bf82`,
  and its 55 compiled Upper/native contracts compared against the current
  library with `audit_ds25.compare`/`query` (the historical audit is not
  redefined to admit DS3 files);
- `python3 tools/audit_public_capabilities.py --check`: all 306 mainline
  public/helper endpoints match the accepted snapshot;
- `python3 -m unittest discover -s tools -p 'test_*.py'`: 58 tests;
- `git diff --check`.

This **joint** kernel check completed with exit status 0:

```sh
opam exec -- coqchk -silent -R _build/default/theories PTree \
  PTree.Prob.Backend.SubEnum.FreeOmega.UpperQuotient \
  PTree.Prob.Backend.SubEnum.FreeOmega.Admissibility \
  PTree.Prob.Backend.SubEnum.FreeOmega.QuotientSoundness \
  PTree.Regression.Probability.FreeOmegaQuotientDomain
```

The four requested modules and their dependencies are the targeted DS3
scope. This is not remote CI or whole-library Gate D. No new axiom or
semantic capability is introduced: the existing classical/extensional
and `eq_rect_eq` dependencies remain explicit in the report.

**Stop here for DS3 acceptance. DS4 has not begun.**
