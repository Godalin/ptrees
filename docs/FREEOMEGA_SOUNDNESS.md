# FreeOmega: external probability semantics and coupling soundness

The completed soundness results validate **admissible `FreeOmega SubEnum`**
in an independent standard subprobability model. They do not interpret every
raw term as a probability, prove syntactic completeness, or supply a
MathComp-native FreeOmega adapter. Program reasoning does not depend on this
validation layer; see [architecture](ARCHITECTURE.md).

## Independent mathematical domain

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

## Native sampling and admissible completion

`SubEnum` consists of finite rational subdistributions. Native expectation
facts live in `Prob/Backend/SubEnum/Expectation.v`; `SubEnum/Domain.v`
interprets this carrier directly into OmegaVal, independently of FreeOmega.

`FreeOmega` remains the sole formal completion syntax: FORet, FOZero,
FOSample and raw FOLub. Its existing `free_omega_upper` is a bounded upper
evaluator on every raw term. A Lub alternating between two distinct Dirac
measures is generally nonadditive, so raw syntax alone is not validity.

`SubEnum/FreeOmega/Admissibility.v` defines `free_omega_admissible` by the
probability-functional laws of that evaluator. `DomainSoundness.v` packages
the evaluator, rather than inventing a second recursive denotation.
Ret/zero, AE-valid sampling/bind, and increasing admissible Lubs are closed;
null native branches may contain invalid terms. The AE/pselect proof does not
strengthen this into everywhere validity. Approximation is sound for bounded
evaluation order, and denotation commutes with bind and increasing Lubs.

## Equality and general relational soundness

`QuotientSoundness.v` uses the all-raw `free_omega_qlift_eq_upper` bridge.
Equal upper evaluators transport admissibility; admissible endpoint equality
is `oval_eq`. The four endpoints are

```text
free_omega_qlift_eq_admissible   free_omega_qlift_eq_sound
free_omega_sem_eq_admissible    free_omega_sem_eq_sound
```

No induction over qlift that assumes valid intermediates is used. In particular
FOQLComp can pass through an inadmissible alternating Lub. Reflexive qlift
does not itself imply admissibility, and zero is not quotient-equal to Dirac.

The general endpoint in `SubEnum/FreeOmega/JointSoundness.v` is, with canonical
SubEnum interfaces understood:

```coq
free_omega_qlift_sound
  (R : realType) {A B} (T : A -> B -> Prop)
  (t : FreeOmega SubEnum A) (u : FreeOmega SubEnum B)
  (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  free_omega_qlift T t u ->
  oval_coupled T (free_omega_domain Ht) (free_omega_domain Hu).
```

This constructs an actual `J : OmegaVal R (A * B)` with both marginals equal
on all bounded tests and concentration on T. Its mass is the common marginal
mass; nothing is conditionally normalized. The support theorem gives zero
expectation to the complement of T. Equality specializes consistently to
the previous equality soundness theorem.

The proof chain is independent countable transport, not a new capability:

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

## Stable-hitting adequacy

`Eq/Backend/StableHittingDomainSubEnum.v` defines a separate mathematical
primitive kernel: Ret/Vis give stable Dirac heads, Tau an internal Dirac state,
and Prob a bind of native subprobability with internal successors. Independent
finite hitting iterates are increasing; their OmegaVal Lub is the behavior.
Finite-fuel commutation connects the existing formal iterates to these values.

With canonical SubEnum/FreeOmega instances understood:

```text
stable_hitting_admissible:
  ptree_stable_hitting s out -> free_omega_admissible R out

stable_hitting_denotational_adequacy:
  ptree_stable_hitting s out ->
  free_omega_domain_denotes out (ptree_domain_hitting R s)

stable_hitting_mass_lub:
  mass(denote out) = sup_n mass(finite mathematical hitting approximant n s)
```

Validity is automatic for every complete witness, not a supplied premise.
There is no AST/eventlessness condition. Complete-hitting uniqueness and
quotient soundness transport the result away from the canonical Lub witness.
The fuel convention sees a current Ret/Vis at zero; Tau/Prob consumes fuel.

Missing mass can mean native subprobability loss **or** failure to reach the
next stable head. It is not unconditionally pure divergence probability.
Infinite visible interaction can have next-head mass one without terminating.
This semantics stops at the next stable head and preserves its whole visible
continuation; it does not construct an infinite interaction-path measure.

`Regression/Probability/IrrationalHitting.v` checks an actual guarded retry
PTree with total rational coins and a rational increasing hitting schedule.
The specialization has limiting hitting mass pi/4, hence irrational. The
construction uses classical choice of rational lower bounds; it is not an
effective algorithm for an arbitrary real parameter and not the RandomWalk
case study in Examples.

## Regression and verification map

| Contract | Maintained regression |
| --- | --- |
| Independent domain, increasing Lub, bounded equality, universe | `Probability/OmegaVal` |
| Countable measure, integrals, missing mass, roundtrips | `Probability/OmegaValMeasure` |
| Raw nonadditivity, native AE, upper/observation/quotient laws | `Backend/FreeOmegaUpperContracts` |
| Invalid raw terms and admissible construction | `Probability/FreeOmegaDomain` |
| Countable coding, explicit plans, actual existence, no escape | `Probability/CountableCoupling` |
| FOQLComp through invalid middle, equality, general joint, high universe | `Probability/FreeOmegaSoundness` |
| Finite real irrational weights / Hall | `Probability/RealTransport` |
| Arbitrary hitting witnesses, partial mass, infinite service | `Probability/StableHittingDomain` |
| Rational coins / irrational limiting mass | `Probability/IrrationalHitting` |

Paths are under `theories/Regression`. The private shared sample fixture is
not a new public API. Raw observation escaping mass and countable matrix mass
escape remain different negative tests. `FreeOmegaLimitSafety` retains the
negative continuity/diagonal/Fubini tests; formal FiniteInternal/Recovery
infrastructure is not deleted by this validation result.

The consolidated compiled contracts retain all 199 non-regression endpoints
from DS1–DS5a audits, alongside the 306 mainline endpoints. Logical dependencies
remain the previously explicit classical choice/extensionality and eq_rect_eq
whitelist; no probability/transport-existence axiom is added. See
[architecture](ARCHITECTURE.md) for reproducible commands and exact kernel-check
scope. Phase reports and exact incremental conservation checks are in git.

Not established: arbitrary invalid-term denotation, syntactic coupling
completeness, MathComp-native external soundness, infinite path measures,
general conditioning, or a completed whole-library Gate D kernel audit.
