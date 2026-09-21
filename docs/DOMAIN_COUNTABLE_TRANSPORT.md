# DS5a.2c: countable transport and no mass escape

Baseline: **finite real Hall transport accepted at `f00478d`**.

The new endpoint is genuine existence on natural-number carriers:

```coq
oval_bidual_coupled_nat :
  forall (R : realType) (T : nat -> nat -> Prop) (L M : OmegaVal R nat),
    oval_bidual T L M -> oval_coupled T L M.
```

The conclusion supplies an actual `J : OmegaVal R (nat * nat)` with the two
bounded-test marginal equalities and `oval_ae J (fun ij => T ij.1 ij.2)`.
It assumes neither a transport plan nor finite support, total mass one, a
decidable relation, or an existence capability. Equal actual masses follow
from `oval_bidual_mass`.

**This closes the nat transport-existence/no-escape step.** It does not yet
export general-carrier coupling existence or `free_omega_qlift_sound`.
Those are the next composition step, using the already accepted coding,
decoding and all-raw qlift-to-bidual bridge. DS5a overall remains OPEN.

## Finite cuts keep both tails

For each cutoff `n`, use the finite carrier `'I_(n+1)`: values `0..n-1` are
ordinary coordinates and coordinate `n` carries the remaining **actual** mass:

```text
pⁿ(i) = p(i)                     if i < n
pⁿ(n) = mass - sum_(i<n) p(i).
```

The same definition applies to `q`. Edges between ordinary coordinates
require `T`; an edge touching either tail coordinate is allowed. Both finite
distributions have exactly the original common mass, including when it is
zero or strictly below one.

`oval_cut_eval` proves that pushing an expectation through this finite
projection gives exactly these weights. Its proof uses bounded additivity,
finite atomic evaluation, and the existing exact tail formula.
`oval_bidual_cut_hall` pulls finite tests back to nat and obtains the finite
Hall inequalities from `oval_bidual`. No family of feasible plans is assumed.

`finite_cut_transport` then applies the accepted **finite real** theorem to
construct each finite matrix, drops its temporary tail row/column, and
extends the ordinary rectangle by zeros.

## The essential lower bounds

For each ordinary row `i` and prefix length `m` within the finite cut:

```text
p(i) - tail_q(m) ≤ sum_(j<m) w(i,j) ≤ p(i).
```

Symmetrically:

```text
q(j) - tail_p(m) ≤ sum_(i<m) w(i,j) ≤ q(j).
```

`finite_transport_row_tail` proves the lower bound by bounding the mass
outside the row prefix by the **entire target capacity outside that prefix**.
This includes the temporary tail coordinate. The transposed argument handles
columns. These are uniform bounds: their errors depend on `m`, not on the
larger finite cut used to produce the matrix.

This is why mass cannot escape to ever larger coordinates. Merely having
coordinatewise convergence, nonnegativity and upper bounds would not suffice.

## Countable compactness and exact marginals

The extended finite matrices lie in the countable-coordinate product box
`[0,mass]^(nat*nat)`. The constraints for stage `n` impose all row/column
prefix bounds with row/column index `< n` and prefix length `≤ n`, as well as
zero weight on all forbidden edges.

The constraints are closed: every individual inequality involves a finite
sum of coordinate projections; arbitrary intersections preserve closedness.
They are nested and nonempty by the finite-cut construction. MathComp product
compactness and the previously proved nested-closed-set lemma give one matrix
satisfying all constraints. Any requested `(index, prefix)` pair is covered
by the stage `max(index+1, prefix)`.

`countable_transport_no_escape` returns this matrix together with both lower
and upper prefix bounds. `transport_prefix_tight_exact` then lets the opposite
tail tend to zero and proves that the supremum of row prefixes is `p(i)`;
likewise for columns. Tightness is derived from `oval_atomic_tight` in the
domain adapter. The missing mass `1-mass` is never mistaken for a disappearing
tail and is never filled in by normalization.

The scalar `countable_real_transport` theorem is independent of OmegaVal.
`oval_bidual_transport_matrix` instantiates every scalar premise and exposes
matrix existence directly from the domain's bidual contract.

## Actual joint realization

`Prob/Domain/Matrix.v` reuses the accepted `oval_series` construction row by
row. A row is a subprobability value of mass exactly `p(i)`; it is **not**
divided by `p(i)`. This avoids any exceptional normalization rule for zero
rows.

The direct mathematical operation `oval_sum` sums a countable family of
OmegaVal values whose finite sums of masses are at most one:

```text
eval (sum c) f = sup_n sum_(i<n) eval (c_i) f.
```

Its evaluator laws, including monotone continuity, are proved from finite
additivity and interchange of bounded suprema. It is not inductive syntax,
a new semantic capability, or another free completion.

Summing the row values, pushed to pairs `(i,j)`, constructs the joint:

- The first marginal follows from exact row masses and atomic representation.
- The second follows from `oval_series_atom`, exact column sums and atomic
  extensionality.
- Relation concentration follows row by row from the existing
  `oval_series_concentrated` theorem; forbidden zero weights contribute nothing.

`oval_matrix_joint` is a matrix-form counterpart to the existing
`oval_transport_plan_joint`. It reuses the same series realization, but does
not force the matrix through a new explicit enumeration of pairs. The old
enumerated-plan theorem and all earlier sources remain unchanged.

## Dependency boundary

```text
Common/RealTransport -> Common/CountableRealTransport
Domain/Expectation  -> Domain/Series -> Domain/Matrix
                         \             /
                     Common/DomainTransport
                              |
                       Regression only
```

The new `Common/DomainTransport` is explicitly classified as a **one-way
external-validation adapter**, not ordinary mainline Common infrastructure.
Only that named adapter may join `Prob/Domain/*` with independent Common
mathematics. `Prob/Domain/*` still imports only `Prob/Domain/*`; ordinary Common
modules still cannot import Domain. Mainline Eq/Interp/API/Examples and native
backend infrastructure cannot depend on the adapter, directly or transitively.

The narrow adapter policy is machine checked, including negative tests.
No facade exports, measure interfaces or FreeOmega definitions change.

## Regression scope

- General successor-relation existence for **any** OmegaVal on nat, entering
  via direct dual inequalities rather than a supplied joint.
- Exact preservation of its actual subprobability mass.
- Zero mass and an empty relation.
- Rejection of unequal masses by the bidual premise.
- A sequence of unit-mass matrices that converges pointwise to zero, and a
  separate proof that it violates the uniform target-tail bound. This checks
  the distinction between pointwise limits and mass-preserving transport.
- The actual scalar matrix endpoint from arbitrary bidual constraints.
- Instantiation of the general existence theorem on the existing unbounded
  geometric retry example (not its previous manually supplied successor plan).
- Imports of the independent existence theory do not load FreeOmega,
  SemanticMeasure, PTree or the MathComp measure adapter.

## Verification protocol

```sh
opam exec -- dune build
python3 tools/audit_countable_transport.py --check
python3 tools/audit_architecture.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
opam exec -- coqchk -silent -R _build/default/theories PTree \
  PTree.Prob.Backend.Common.CountableRealTransport \
  PTree.Prob.Domain.Matrix \
  PTree.Prob.Backend.Common.DomainTransport \
  PTree.Regression.Probability.CountableTransportExistence
```

The source audit freezes all 245 earlier `.v` files byte-for-byte except four
exact aggregate imports, and permits only the four new modules. The compiled
audit covers 26 endpoints and retains the existing logical-axiom whitelist.
Earlier compiled signature/assumption snapshots are compared independently;
earlier incremental source audits are replayed at their accepted revisions.
Targeted recursive kernel checking is not the whole-library Gate D audit.

### Local verification results

- Full `dune build`, including `AllImports`: passed.
- Four new modules jointly checked by recursive `coqchk`, without `-admit`:
  passed, including the geometric integration test's dependencies.
- Exact preservation of 245 earlier sources, plus four explicit aggregate
  imports: passed.
- 26 compiled contracts and their logical assumptions: passed against the
  unchanged whitelist.
- Ownership/dependency audit and all 85 audit-tool unit tests: passed.
- DS1a/DS1b/DS2/DS2.5/DS3/DS4/DS5a.1/DS5a.2a/DS5a.2b compiled snapshots:
  unchanged, with the existing namespace normalization where required.
- 306 public/helper and 25 capability endpoint snapshots: unchanged.

The core nat-existence theorem inherits the existing propositional and
functional extensionality and indefinite-description assumptions. It does
not add a probability or transport axiom. These are local checks; no remote
CI result is claimed.
