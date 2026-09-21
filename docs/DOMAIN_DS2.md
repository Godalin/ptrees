# DS2: SubEnum and admissible FreeOmega in the external domain

Baseline: **DS1b accepted at `01cbc4c`**. DS2 implements the first arrow

```text
admissible FreeOmega SubEnum
           ↓ existing upper evaluator, packaged with proved laws
         OmegaVal
           ↓ DS1b, on the discrete lifted carrier in its adapter universe
standard countably additive probability measure
```

This stage does not change DS1a/DS1b or the maintained FreeOmega/Eq/Interp
theory. There is no new completion syntax, recursive evaluator, quotient
definition or backend capability. Pause for acceptance before DS3.

## Native interpretation

`Prob/Backend/SubEnum/Domain.v` defines `subenum_domain R mu` by the existing
finite rational weighted expectation `enum_real_expect f (subenum_raw mu)`.
Finite-sum algebra proves scaling/additivity, `subenum_bound` proves the
mass bound, and the existing finite expectation/supremum interchange proves
monotone continuity. Thus `subenum_domain_laws` is proved, not assumed.
At the accepted DS2 baseline `bc8f9d2`, those facts lived in the SubEnum
`UpperExpectation/UpperCoupling/UpperContinuity` modules. The strictly
conservative [DS2.5 follow-up](DOMAIN_DS25.md) moves their finite dependency
closure to `Prob/Backend/SubEnum/Expectation.v`. The native adapter now has
no transitive FreeOmega dependency; the independent **Domain** itself remains
entirely separate. The accepted DS2 compiled snapshot is retained unchanged.

Endpoints cover ret, zero, bind and native semantic equality. The native
`subenum_sem_lift_test_sound` theorem gives relational test inequalities;
it does not claim a newly constructed external joint coupling.

## Semantic admissibility, not a syntax discipline

`Prob/Backend/SubEnum/FreeOmega/Admissibility.v` defines

```coq
free_omega_admissible R t :=
  OmegaValLaws (free_omega_upper (R := R) t).
```

`free_omega_domain H` uses **exactly** that existing evaluator and the proof
`H`. There is no choice of a denotation representative and no new recursive
interpretation. Different admissibility proofs give observationally equal
domain values, by reflexivity rather than proof irrelevance.

`free_omega_domain_denotes t L` means equality on all bounded tests. The name
deliberately avoids shadowing the existing internal `free_omega_denotes`.
We prove

```text
admissible R t ↔ ∃ L : OmegaVal R A, free_omega_domain_denotes t L.
```

Ret, zero, Sample and bind are closed under admissibility. For Lub, the
theorem requires admissible members and an **increasing denotation**; the
convenience theorem `admissible_lub_approx` discharges that condition using
`free_omega_approx eq` between successive raw terms. Closure is obtained
from the already-proved `oval_lub` construction, not by adding a Lub axiom.

This is a sufficient construction rule, not the definition of admissibility:
we do not require every raw Lub subterm to carry a syntactic increasingness
certificate. Nor do we assert that every non-increasing sequence is invalid.
What is false, and explicitly refuted below, is **unconditional** raw Lub
admissibility.

### AE closure is included now

Both `admissible_sample_ae` and `admissible_bind_ae` are proved. Their premises
are respectively native `sem_ae` and the existing structural `free_omega_ae`.
This lets null-probability branches remain inadmissible.

The proof-only `admissible_support_kernel` uses classical `pselect` to leave
admissible branches unchanged and replace other branches by zero. The AE
premise and existing `free_omega_upper_ae_ext` prove that this replacement
does not change any bounded expectation of the compound computation.
Pointwise closure then applies. This is not a denotation assigned to invalid
raw terms, and it is never used without the explicit AE support premise.
It chooses no representative in `OmegaVal`.

## Algebra and approximation soundness

`Prob/Backend/SubEnum/FreeOmega/DomainSoundness.v` proves:

- `free_omega_denote_ret`, `free_omega_denote_zero`, `free_omega_denote_native`;
- `free_omega_denote_sample` and `free_omega_denote_sample_ae`;
- `free_omega_denote_bind` and `free_omega_denote_bind_ae`;
- `free_omega_denote_lub`: an increasing chain of domain denotations denotes
  precisely the mathematical `oval_lub`;
- `free_omega_denote_approx`: raw equality approximation implies `oval_le`
  between domain denotations;
- `free_omega_denote_approx_test`: heterogeneous approximation preserves
  relational inequalities between bounded tests.

The bind equation uses the existing **unconditional** upper-evaluator bind
identity, then equality of bounded expectations. Lub is the same scalar
supremum on both sides. Order uses the existing raw approximation inequality.
These are external-domain theorems, not an internal FreeOmega observation
judgment relabelled as adequacy. General relational **joint-coupling**
realization is still DS5a, not an interpretation of the last test theorem.

## Checked boundaries

`Regression/Probability/FreeOmegaDomain.v` proves:

- Alternating Boolean Diracs have singleton expectations both equal to one,
  while their sum has expectation one. Bounded additivity gives a
  contradiction: `alternating_bool_not_admissible`.
- By the existence characterization, that raw term has **no** domain model.
- An explicitly present zero-weight branch may contain that invalid term;
  Sample and bind remain admissible, and the AE denotation theorem works.
- The same invalid branch reached with positive weight is rejected.
- A delayed increasing chain is admissible and denotes its domain Lub;
  approximation becomes domain order, and native bind denotes domain bind.
- A fair-coin retry chain with unbounded depth is admissible and denotes its
  Lub. This test requires no AST/mass-one premise and does not claim an AST
  theorem or solve an irrational-limit example in this stage.
- Importing the new adapters does not load `MeasureModel`, PTree or peutt.

The architecture checker enforces the converse boundary: no mainline tree,
equational, interpreter, API or example module depends on these validation
adapters, even transitively. The aggregate now covers 228 modules in total.

## Logical assumptions and verification

The [compiled audit](DOMAIN_DS2_AUDIT.md) covers 51 entries, including three
**existing** bridge theorems so their inherited assumptions are visible next
to the new endpoints. DS1a/DS1b snapshots are not modified.

Besides DS1's classical/extensional assumptions, the old native coupling
bridge uses Coq `Classical_Prop.classic` and
`Description.constructive_definite_description`; the old dependent
structural-AE bridge uses `Eqdep.Eq_rect_eq.eq_rect_eq`. The audit explicitly
permits and records these inherited dependencies. No new axiom declaration,
admitted proof or semantic capability premise is introduced. This is not a
constructivity or UIP-free claim.

Passed locally: full dune build/AllImports, architecture and aggregate
checks, unchanged DS1a/DS1b and 306-entry mainline snapshots, the 51-entry DS2
snapshot, and 47 tool tests. A single targeted `coqchk -silent` invocation
also passed for the three new theory modules, `FreeOmegaDomain` regression,
and `AllImports`, with `-norec` for those five modules and default conversion.
The formal three-module subset passed an additional targeted run. These
checks do not recursively recheck external dependencies and are not the
pending Gate D whole-library audit. No remote CI result is claimed.

DS3 (`qlift eq` / FreeOmega `sem_eq` soundness and admissibility transport),
DS4 (stable-hitting adequacy), and DS5a (general joint coupling) are not started.
