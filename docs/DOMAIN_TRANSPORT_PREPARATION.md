# DS5a.2 preparation: atomic normal form and transport-plan realization

Baseline: **DS5a.1 accepted at `086f2c1`**.

**DS5a.2 is not complete.** This increment proves the representation and
realization steps around the remaining existence problem. It does not prove
that Hall/bidual constraints produce a transport plan, and it does not export
`countable_transport_exists` or `free_omega_qlift_sound`.

## Proven mathematical reduction

```text
countably supported L, M + bidual T
    |
    | oval_countable_transport_reduction
    v
N, K : OmegaVal nat + bidual on the decoded relation
    |
    | OPEN: construct nonnegative real edge weights with exact row/column sums
    v
an actual enumerated transport plan
    |
    | oval_transport_plan_joint
    v
J : OmegaVal (nat * nat), with exact marginals and relation concentration
    |
    | oval_joint_decode
    v
an external joint for L, M on the original carriers
```

No general existence principle is a hypothesis or typeclass in this work.
`oval_transport_plan_joint` takes **the actual scalar weights**, proves that
their series is an OmegaVal, and proves its joint laws. This is conditional
realization of a supplied plan, not a proof that such a plan exists.

## Atomic normal form and tightness

`Prob/Domain/Atomic.v` defines the mass of atom `i` by the expectation of
its singleton indicator. From bounded additivity and continuity it proves:

```text
eval L f = sup_n sum_(i < n) atom(L,i) * f(i)
mass L   = sup_n sum_(i < n) atom(L,i)
```

All tests are `[0,1]`-valued. Equal atom masses imply `oval_eq`, not record
equality and not equality on unbounded observables. This upgrades DS5a.1's
code/decode representation to an actual atomic-series normal form on nat.

`oval_atomic_tight` proves that for every positive epsilon there is a
finite prefix whose missing **actual mass** is below epsilon.
`oval_atomic_tail` identifies that remainder exactly with the expectation
of the tail indicator. If `mass L < 1`, the intrinsic missing mass is not
mistaken for a tail that should eventually disappear.

These facts are available for the later tightness argument needed when
passing to a limit of finite transport plans. No compactness or extraction
of a limiting plan is claimed by this increment.

## Direct series construction, with real weights

`Prob/Domain/Series.v` constructs `oval_series` from weights
`w : nat -> R`, nonnegativity, and finite-prefix sums bounded by one:

```text
eval (series w) f = sup_n sum_(i < n) w(i) * f(i)
```

The evaluator laws are proved, not supplied as extra premises. In
particular, bounded additivity uses increasing prefix sums; monotone
continuity commutes a finite sum with a countable supremum and then swaps
two bounded countable suprema. There are no constructors and no second
free completion. The weights may be arbitrary reals, not just rationals.

`oval_series_roundtrip` reconstructs every `OmegaVal nat` up to bounded
observational equality from its atom masses.

For an edge enumeration `edge : nat -> nat * nat`,
`oval_transport_plan_joint` pushes the series through `edge`. Its premises
are exact scalar row/column sums and that every nonzero edge weight is on
the desired relation. Atomic extensionality upgrades the scalar equations
to full bounded-test marginal equalities. Concentration follows term by
term, with zero weights contributing nothing. Repeated edges are allowed.

## Coding and decoding arbitrary carriers

`Prob/Domain/CountableTransport.v` first proves an AE-restriction lemma
for dual inequalities by masking the left test to zero and the right test
to one outside their respective concentration sets. Thus zero-mass values
cannot obstruct transport to the code relation.

`oval_coded_bidual` then pushes both marginals through the existing chosen
code functions. A pair of codes is related exactly when it decodes to a
pair in the original relation. Neither enumeration need be injective.
The original carriers need not be countable, inhabited, or equipped with
decidable equality.

`oval_joint_decode` maps a valid code pair to a Dirac pair of values and
an invalid pair to bottom. This does not lose mass: the incoming joint's
concentration on the code relation ensures that both codes are valid almost
surely. The theorem proves the original marginals and relation concentration
for the result. It does not normalize either marginal.

`oval_countable_transport_reduction` **constructs** coded marginals and their
constraints, together with the proved decoding implication for any actual
coded joint. It does not take or declare a universal nat-transport capability.

## Regression scope

`Regression/Probability/CountableTransport.v` checks:

- independent imports do not load FreeOmega, SemanticMeasure, PTree or the
  MathComp measure adapter;
- an explicit successor-edge plan for **any** `OmegaVal nat`, without
  finite-support or total-mass assumptions;
- that plan instantiated on the previously checked unbounded geometric
  retry behavior;
- exact tail tightness relative to actual subprobability mass;
- duplicated valid codes and invalid `None` codes;
- code-domain bidual constraints with duplicated enumerations;
- decoding with arbitrary missing mass, without a totality assumption;
- an empty original carrier and the zero joint;
- atomic extensionality.

The generic successor-plan regression is not a general existence proof:
its relation has a known explicit plan. The geometric instantiation does
not add a new theorem computing all geometric atom weights.

## Remaining core obligation

Given nat marginals and the setwise Hall/bidual inequalities, construct
nonnegative real weights with the required exact row and column sums and
relation support. That implication remains wholly open here. The existing
finite **rational** transport theorem does not by itself solve the finite
real or countably infinite problem. A finite-feasibility/compactness proof
is a possible next route, not an implemented theorem.

The frozen all-raw qlift-to-bidual bridge remains the eventual source of
the constraints. Nothing in this increment recurses on qlift or requests
admissibility for `FOQLComp` intermediates.

## Verification

`audit_domain_transport.py` compares all 239 baseline `.v` files
byte-for-byte, permitting only four exact aggregate imports. It audits
30 compiled endpoints against the unchanged logical-axiom whitelist and
rejects added semantic axioms/classes or premature general-existence names.
The historical DS1–DS5a.1 compiled snapshots are checked separately without
regeneration; source audits for earlier increments use their frozen commits.

The new proof modules remain in the independent validation-only Domain
layer. The mainline dependency boundary is unchanged. Kernel verification
is a targeted joint recursive `coqchk` of the three Domain modules and their
regression, not the deferred whole-library Gate D audit.

Verification completed for this increment:

- full `opam exec -- dune build`, including AllImports;
- 76 audit-tool unit tests and the 243-module architecture/aggregate checks;
- exact 239-module source conservation and the 30-endpoint compiled audit;
- unchanged DS1a/DS1b/DS2/DS2.5/DS3/DS4/DS5a.1 compiled contracts, including
  the already-reviewed DS2.5 relocation normalization for the DS2 snapshot;
- unchanged 306-entry public/helper and 25-entry capability snapshots;
- joint recursive `coqchk -silent` on `Atomic`, `Series`,
  `CountableTransport` and its regression, completed with exit status 0,
  without `-admit`;
- no new semantic axiom, typeclass or admitted proof.
