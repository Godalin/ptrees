# DS5a, first increment: countable support and dual constraints

Baseline: **DS4 accepted at `10b5563`**. The core domain-soundness line is
finished. DS5a is an optional strengthening; this first increment is
**not completion of DS5a** and does **not** assert a general joint
realization theorem.

## Implemented boundary

```text
raw FreeOmega SubEnum term
    -> explicit enumerable support cover

admissible endpoint
    -> OmegaVal concentrated on that cover
    -> mass-preserving representation over a natural-number carrier

qlift T t u, with admissible endpoints only
    -> existing all-raw bounded-test inequalities
    -> external bidual constraints
    -> equal masses and setwise Hall inequalities

qlift eq t u, with admissible endpoints
    -> DS3 equality
    -> explicit diagonal external joint
```

The missing implication is still:

```text
countably supported OmegaVal marginals + bidual constraints
    -> existence of a joint OmegaVal with those marginals and T-support.
```

No axiom, class, hypothesis, or constructor assuming this implication has
been introduced. No general `free_omega_qlift_sound` is exported. In
particular, test-function soundness is not renamed into joint existence.

## Countable support, without a countable result type

`Prob/Backend/SubEnum/FreeOmega/CountableSupport.v` defines
`free_omega_enumerate t : nat -> option A`. It traverses native finite
sample lists and countably indexed formal Lubs, using the standard
natural-pair coding. A structural proof gives:

```coq
free_omega_enumerate_covers :
  free_omega_ae
    (fun x => exists n, free_omega_enumerate t n = Some x) t.
```

This holds for **all raw terms**, including inadmissible ones. It is a
cover, not an injective enumeration or a characterization of the positive
atoms. Zero-weight entries may be included. No countability, inhabitedness,
or decidable equality of the result type is assumed.

`Prob/Domain/Countable.v` is independent of FreeOmega and the semantic
interfaces. It defines concentration `oval_ae L P` by invariance of all
bounded expectations under changes outside `P`. On admissible endpoints,
the raw AE theorem and the existing scalar AE-extensionality lemma prove
this mathematical concentration property.

The independent `oval_countable_representation` theorem constructs a
measure on natural-number codes. Classically choose a code for every
covered value and push `L` through that code function. Its result `N`
satisfies:

```text
mass N = mass L
N is concentrated on valid codes
L ≈ bind N (decode e)
```

Here `decode e n` is Dirac at `x` if `e n = Some x`, and bottom otherwise.
The concentration property makes the arbitrary fallback code for uncovered
values irrelevant. `N` is an actual OmegaVal, not a free syntax or a
supplied representation premise. DS1b supplies its standard countably
additive measure interpretation. This is a countable-carrier pushforward
representation; an explicit infinite atomic-sum normal form is not claimed.

## A joint is a mathematical measure, not another lifting constructor

`Prob/Domain/Coupling.v` defines `oval_joint T L M J`, where
`J : OmegaVal R (A * B)`, by:

```text
eval J (f ∘ fst) = eval L f      for every bounded test f
eval J (g ∘ snd) = eval M g      for every bounded test g
J is concentrated on {(x,y) | T x y}.
```

`oval_coupled T L M` means that such a `J` exists. The marginals preserve
the original subprobability mass, without normalization. The theorem
`oval_joint_off_relation_zero` additionally exposes concentration as zero
expectation of the complement indicator, hence zero complement measure
under DS1b. This is measure concentration, not topological support.

The new mathematical dual relation is stated separately:

```text
oval_dual T L M :=
  forall bounded f,g,
    (forall x,y, T x y -> f x <= g y)
    -> eval L f <= eval M g.
```

`oval_bidual` includes the converse direction. A joint implies bidual
constraints (`oval_joint_dual`). Testing constant one proves equality of
mass. Testing indicators of `P` and its relational image proves the full
setwise Hall condition:

```text
L(P) <= M({y | exists x, P(x) and T(x,y)}).
```

For equality, the diagonal `bind L (fun x => ret (x,x))` is already an
explicit joint whenever `oval_eq L M`. Thus `oval_coupled eq L M` is
equivalent to `oval_eq L M`, and the backend equality-joint endpoint is a
direct consequence of the frozen DS3 theorem.

## FOQLComp: the raw intermediate is not interpreted as a measure

`Prob/Backend/SubEnum/FreeOmega/CouplingSoundness.v` applies the existing
`free_omega_qlift_upper_birel` directly. That theorem has already proved the
test inequalities on all raw terms, using bounded fiber envelopes for
composition. The new bridge performs no induction on qlift and requests
admissibility only for the two endpoints.

The regression explicitly composes through DS2's inadmissible
`alternating_bool`, with distinct unit/bool endpoint carriers and relation
`fun (_ : unit) b => b = true`. It establishes external bidual constraints
from that actual derivation. Another test constructs an equality joint
through DS3's explicit bad-middle derivation. Countable coverage of the
bad middle is also checked, alongside its lack of admissibility.

Additional checks cover an empty carrier, geometric prefixes over an
unbounded natural-number return carrier, mass-preserving code/decode
representation, a zero joint supported on the empty relation, impossibility
of a positive joint on the empty relation, and rejection of unequal masses.

## What remains in DS5a

The next substantial mathematical lemma belongs in the independent domain,
not in the qlift induction:

```coq
(* Planned statement, NOT an implemented theorem or assumed capability. *)
countable_transport_exists :
  oval_countably_supported L ->
  oval_countably_supported M ->
  oval_bidual T L M ->
  exists J, oval_joint T L M J.
```

Once proved, `free_omega_qlift_countable_constraints` provides all its
premises. This route handles raw/inadmissible intermediates without ever
requiring joints for those intermediates. It establishes soundness of
qlift, not the reverse completeness of the syntactic lifting.

The available repository transport theorem is `finite_rational_transport`:
it covers finite carriers and rational weights. It cannot directly solve
countably many real-valued atom masses. A possible next proof route is
finite fractional transport followed by a tight countable limiting
construction. That limiting construction and preservation of exact
marginals/support must be proved, not assumed; no route has yet been
machine-checked here. The elementary existing equality-joint result must
not be mistaken for that general theorem.

## Isolation and verification

The two Domain modules depend only on Domain. Both backend modules are
classified as external validation, and are excluded from mainline API,
Eq, Interp and Examples dependency closures. No MathComp-native adapter,
PTree stable-hitting change, FiniteInternal cleanup, path measure, AST
theory, or public API restructuring is included.

`audit_domain_relational.py --source` freezes all 234 DS4 baseline `.v`
files byte-for-byte except five exact aggregate imports. The only theory
additions are the two Domain modules, two validation adapters, and one
regression. The compiled audit covers 39 endpoints, retaining the DS2-DS4
logical-axiom whitelist and checking that validity has not disappeared
from backend signatures. Earlier snapshots are not regenerated.

Completed local checks:

- Full `opam exec -- dune build`, including AllImports;
- Aggregate inventory: all 238 other modules imported exactly once;
- `audit_domain_relational.py --check`: frozen source isolation and the
  [39-entry compiled signature/assumption report](DOMAIN_DS5A_FOUNDATIONS_AUDIT.md);
- `audit_architecture.py --check`: ownership and one-way validation boundary;
- DS1a/DS1b/DS2 compiled snapshots unchanged (37/37/51 endpoints);
- DS2.5, DS3 and DS4 source audits replayed against their frozen revisions,
  with their 55/19/38 compiled contracts unchanged in the current library;
- Mainline 306-entry and original 25-entry compiled capability audits unchanged;
- `python3 -m unittest discover -s tools -p 'test_*.py'`: 71 tests;
- `git diff --check`.

The following **joint recursive kernel check** completed with exit status 0:

```sh
opam exec -- coqchk -silent -R _build/default/theories PTree \
  PTree.Prob.Domain.Countable \
  PTree.Prob.Domain.Coupling \
  PTree.Prob.Backend.SubEnum.FreeOmega.CountableSupport \
  PTree.Prob.Backend.SubEnum.FreeOmega.CouplingSoundness \
  PTree.Regression.Probability.FreeOmegaRelationalDomain
```

This is a five-module targeted check with dependencies, not remote CI or
whole-library Gate D. There are no newly declared axioms or admitted
proofs. This first increment pauses for review; **DS5a remains in progress**.
