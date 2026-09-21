# DS1b: standard countably additive measure correspondence

Baseline: **DS1a accepted at `e65ca85`**. DS1b is implemented and ready for
review. This stage adds the independent measure adapter and its tests;
it does not connect FreeOmega to the domain or begin DS2.

## Mathematical model

`Prob/Domain/MeasureModel.v` imports `Expectation` and MathComp's ordinary
measure/integration libraries. It imports no native backend, SemanticMeasure
interface, FreeOmega, tree syntax, or equational theory. The domain remains
the DS1a evaluator/laws record; there is no second free syntax.

The main correspondence is

```text
OmegaVal R A / oval_eq
       ↔
MathComp probability measures on the discrete space A⊥,
compared by their values on every set.
```

`oval_carrier A = OVBottom | OVValue A` is an ordinary lifted carrier with
the powerset sigma-algebra. The adapter uses MathComp/HB's ordinary
monomorphic carrier universe, with universe minimization disabled. It does
not claim that every higher-universe carrier can be installed as a MathComp
measurableType. The accepted polymorphic `Expectation.v` is unchanged, and
its high-universe regression still builds.

The completed probability measure satisfies

```text
oval_probability L {OVBottom} = (1 - oval_mass L)%:E
oval_probability L (oval_values U) = (L (indicator U))%:E
```

Thus bottom encodes missing mass; the value part is a standard
subprobability measure. The total measure on `A⊥` has mass exactly one,
including when `A` is empty. `%:E` embeds a real in MathComp's extended reals.

## Countable additivity is proved

For a measurable carrier `T`, define

```text
oval_set_measure L U = (oval_eval L (indicator U))%:E.
```

Finite additivity follows from bounded additivity applied to disjoint
indicators. For a disjoint sequence of measurable sets, the finite unions
have increasing indicators whose pointwise supremum is the indicator of
the union. `oval_continuous` identifies the union's mass with the limit of
the finite sums. This proves `oval_set_measure_sigma_additive`, the actual
MathComp `semi_sigma_additive` obligation. Positivity and the empty-set law
then build a MathComp measure; the mass bound builds `oval_subprobability`.
Countable additivity is not an extra hypothesis.

For the probability completion, `oval_complete L` evaluates `f : A⊥ -> R` as

```text
L (fun a => f (OVValue a)) + (1 - mass L) * f OVBottom.
```

Its laws and total mass are proved. Additivity is real algebra; continuity
uses DS1a's scaling/sum supremum lemmas. The preceding construction then
gives the genuine MathComp `probability` record `oval_probability L`.

## Integration recovery and reverse construction

`oval_integral_recovery` proves, for any bounded **measurable** `f` on `T`,

```text
∫ EFin(f) d(oval_set_measure L) = EFin(L f).
```

The proof first handles nonnegative simple functions via their finite
indicator decomposition (`oval_simple_integral`). MathComp's nonnegative
simple approximants increase to `f`; its integral limit theorem and
evaluator continuity give recovery. There is no integration-recovery
axiom or additional probability typeclass.

Conversely, on a space where every set is measurable, a standard
subprobability measure gives the evaluator

```text
measure_oval_eval μ f = fine (∫ EFin(f) dμ).
```

On `[0,1]` tests the integral lies in `[0,1]`, so it is finite and `fine`
recovers its real value. Positivity, linearity and monotonicity follow from
MathComp integral theorems; `measure_oval_eval_continuous` uses its monotone
convergence theorem. These proofs construct `measure_oval_laws` and
`measure_oval`, not assumptions about a new interface. No behavior on
unbounded tests is claimed.

For a probability `p` on `A⊥`, `probability_oval p` evaluates a test after
extending it by zero at bottom, using this integral evaluator and DS1a's
proved bind. The principal endpoints are:

```text
oval_probability_integral:
  oval_test f → ∫ EFin(oval_extend f) d(oval_probability L) = EFin(L f)

oval_probability_roundtrip:
  oval_eq (probability_oval (oval_probability L)) L

probability_oval_roundtrip:
  ∀ U, oval_probability (probability_oval p) U = p U
```

The reverse roundtrip includes sets containing bottom, not only returned
values: total mass forces bottom's mass to be the complement of value mass.
Neither roundtrip asserts raw record equality or uses proof irrelevance.
The intermediate subprobability endpoints are `oval_measure_roundtrip`,
`measure_oval_roundtrip`, and `oval_measure_extensional`.

## Validation and boundaries

`Regression/Probability/OmegaValMeasure.v` checks bottom/Dirac measures,
distinct returned Diracs, a half-mass evaluator, both arbitrary roundtrips,
and the empty carrier. Three `Fail Check` probes verify that importing the
model does not load FreeOmega, SemanticMeasure or PTree. Architecture rules
also verify that the mainline cannot depend on the model, including through
an intermediate backend adapter.

Local checks passed:

- Full `opam exec -- dune build`, including AllImports (224 modules total).
- Aggregate inventory and architecture `--check`.
- All 306 frozen public/helper compiled signatures and assumptions unchanged.
- DS1a's separate 37-endpoint compiled snapshot unchanged.
- DS1b's [37-endpoint compiled audit](DOMAIN_DS1B_AUDIT.md), using exactly
  DS1a's logical-axiom whitelist, with negative audit-tool tests.
- 43 audit-tool unit tests.
- One targeted `coqchk` process for `MeasureModel`, `OmegaValMeasure` and
  `AllImports`, using `-norec` for those modules and default conversion.

This is **not** the pending Gate D whole-library audit; external dependencies
are not recursively rechecked by that command. No remote CI result is
claimed. Logical assumptions are the existing classical choice and
extensionality assumptions recorded by the audit, not newly declared axioms,
admitted proofs or semantic capability hypotheses.

This closes the independent domain's standard-measure foundation. It does
**not** yet prove FreeOmega admissibility, equality/coupling soundness or
stable-hitting adequacy. Those remain the later DS stages. Pause here for
DS1b acceptance.
