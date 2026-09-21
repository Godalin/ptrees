# DS5a.2: finite real Hall transport existence

Baseline: **DS5a.2 transport preparation accepted at `c189a2e`**.

This increment proves **finite real transport existence**, not the remaining
countably infinite transport theorem. DS5a.2 and general relational qlift
joint realization remain **OPEN**. The earlier atomic-series, coding and
decoding results are unchanged.

## What is now proved

For finite carriers `X`, `Y`, nonnegative real demands `p`, capacities `q`,
and a bipartite edge relation, assume the weighted Hall inequalities:

```text
for every S ⊆ X,  sum_(x ∈ S) p(x) ≤ sum_(y ∈ neighbors(S)) q(y).
```

`finite_real_subtransport` constructs an actual matrix `w : X -> Y -> R`:

```text
w(x,y) ≥ 0
sum_y w(x,y) = p(x)
sum_x w(x,y) ≤ q(y)
not edge(x,y) -> w(x,y) = 0.
```

`finite_real_transport` additionally assumes equal total masses and proves
**both marginals exactly**. There is no total-mass-one assumption, no rational
weight restriction, and no inhabitedness premise on either finite carrier.

`finite_real_transport_of_tests` obtains Hall from the bounded-test dual
inequalities by indicator tests. `finite_real_transport_relation` exposes
the same result for an arbitrary **Prop-valued** relation; classical `asbool`
is internal, and no decidable-relation hypothesis is added to the statement.

These theorems construct the weights. They do not take a transport plan or
a transport-existence capability as a premise.

## Proof route

1. **Integer subtransport.** Reuse the existing `capacity_hall_matching`
   theorem on capacity copies. Count the matched copies to obtain exact
   source rows and target columns bounded above by their capacities. Unequal
   total capacity is permitted; a perfect matching theorem alone would not
   suffice for the next step.
2. **Real rounding.** At denominator `d > 0`, round each `d*p(x)` down and
   each `d*q(y)` up using `floor(d*q(y)) + 1`. The real Hall inequalities
   imply integer Hall for these rounded capacities. Divide the resulting
   integer matrix by `d`. Rows lie in `(p(x)-1/d, p(x)]`; columns are at most
   `q(y)+1/d`. Forbidden edges remain exactly zero.
3. **Compactness removes rounding.** Matrices lie in the product box
   `[0, sum_x p(x)]^(X×Y)`. MathComp's product compactness theorem and compact
   real segments prove compactness of this box. The closed constraints with
   error `1/(n+1)` are nested and nonempty. A cluster point satisfies every
   error bound, hence exact rows and column upper bounds.
4. **Equal mass removes slack.** Under equality of the two total masses, all
   nonnegative column deficits sum to zero. Each deficit is therefore zero.

All compactness and limit steps are proved using the installed MathComp
topology/real theory. No new probability interface, free construction, axiom,
or admitted theorem is introduced. The logical assumptions are recorded in
`DOMAIN_REAL_TRANSPORT_AUDIT.md`, using the unchanged DS1–DS5 whitelist.

## Placement and isolation

`Prob/Backend/Common/RealTransport.v` is pure finite arithmetic/combinatorics
and topology. It depends on the existing `FiniteMatching` and
`FiniteCapacityMatching`, not on Enum, SubEnum, MathComp-native measures,
OmegaVal, SemanticMeasure, FreeOmega or PTree. Thus it belongs to the existing
backend-independent `Common` infrastructure. It is not exported by a public
PTree facade. No ownership or dependency rule is weakened.

The regression imports also explicitly check that none of the probability
domain, formal measure interface, FreeOmega syntax or tree theory is loaded.

## Regression coverage

- Diagonal transport for arbitrary nonnegative real masses.
- A real `sqrt(2)` weight, without rationality assumptions (the test does not
  separately prove irrationality of `sqrt(2)`).
- Source demand with unused target capacity.
- One source row split across two independently weighted target columns.
- Empty source and arbitrary nonnegative target capacities.
- Empty target with zero source demands.
- Impossibility of transporting positive mass to an empty target.

The splitting and slack examples invoke the existence theorems, not manually
provided matrices. The negative empty-target case verifies the boundary of
the Hall premise.

## Remaining mathematical obligation

The desired result is still:

```text
countably supported OmegaVal marginals + bidual/Hall
    -> nonnegative countable transport plan with exact marginals
    -> standard external joint coupling.
```

Finite exact existence does not by itself imply countable exact existence:
mass could escape to larger and larger coordinates in a naive limit. A
next proof must preserve tightness while constructing and limiting finite
truncations. The existing `oval_atomic_tight` and `oval_atomic_tail` provide
the relevant control relative to **actual marginal mass**, not one.

One possible route is to collect the target tail into a temporary capacity
column, use finite subtransport, and impose closed lower as well as upper
bounds on finite row prefixes before taking a product-space cluster point.
That countable argument is **not implemented by this increment**. No theorem
named `countable_transport_exists` or `free_omega_qlift_sound` is claimed.

The eventual FreeOmega bridge must continue to use the all-raw
`free_omega_qlift_upper_birel` result. No part of this increment adds validity
requirements on qlift derivation intermediates.

## Reproducible checks

```sh
opam exec -- dune build
python3 tools/audit_real_transport.py --check
python3 tools/audit_architecture.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
opam exec -- coqchk -silent -R _build/default/theories PTree \
  PTree.Prob.Backend.Common.RealTransport \
  PTree.Regression.Probability.RealTransport
```

The source audit preserves all 243 baseline `.v` files byte-for-byte, except
the two explicit aggregate import insertions. It permits exactly the two new
modules, rejects added assumptions, and checks the finite existence endpoints.
The compiled audit checks 18 mathematical/regression endpoints and their
logical assumptions. Earlier compiled contracts are checked independently;
earlier incremental source audits are replayed on their accepted revisions.
This targeted recursive kernel check is not a whole-library Gate D audit.

### Local verification of this increment

- Full `dune build`, including `AllImports`: passed.
- Two new modules jointly checked by recursive `coqchk`, without `-admit`: passed.
- Exact source-isolation and 18-endpoint compiled audit: passed.
- Architecture/dependency audit and all 80 audit-tool unit tests: passed.
- DS1a, DS1b, DS2, DS2.5, DS3, DS4, DS5a.1 and DS5a.2a compiled
  snapshots: unchanged (using the existing DS2.5 namespace normalization).
- The 306 public/helper and 25 capability endpoints: unchanged.

These are local results; no remote CI success is claimed.
