# Finite discrete backends

## Representation

The maintained carriers specialize shared invariant-bearing records:

```text
EnumQ A       = FiniteEnum rat A
SubEnumQ A    = FiniteSubdist rat A
SubEnumR R A  = FiniteSubdist R A
```

Coefficients are ordinary scalars. `FiniteEnum` carries nonnegativity of the
whole list; `FiniteSubdist` additionally carries mass at most one. Shared
finite algebra works over `numDomainType`. Result carriers need no equality,
countability or inhabitation assumption.

Order, duplicate atoms and zero entries are retained. There is no implicit
coercion to a raw list: `enumQ_raw` and `subenumQ_data` expose lists, whereas
`subenumQ_raw` exposes a checked `EnumQ`. Constructors with arbitrary rational
weights require their nonnegativity evidence. Ordinary probabilistic programs
should use `SubEnumQ` or `SubEnumR`; weighted `EnumQ` is not automatically a
subprobability distribution.

`nnQ` is legacy, not a maintained carrier coefficient. There is no production
old/shared conversion layer. The historical representation certificate has
also been retired from Regression; its preservation evidence remains in Git.

## Shared mathematics and backend ownership

The common files live in `Prob/Backend/Common`:

| Owner | Responsibility |
| --- | --- |
| `FiniteEnum`, `FiniteSubdist` | Checked containers, operations and expectation |
| `FiniteListAlgebra`, `FiniteAtoms` | Raw weighted-list algebra and atom mass |
| `FinitePositions` | Position indexing, including zero entries |
| `FinitePruning` | Order-preserving removal, without aggregation or normalization |
| `FinitePresentation`, `FiniteIndexedBind` | Finite positional presentations and bind indexing |
| `FiniteSupport` | Support/expectation facts with explicit nonnegativity requirements |
| `FiniteScalarMap` | Scalar transport and preservation of checked operations |

Deleting zero entries preserves expectation even for signed observables.
Arbitrary pruning only gives an expectation inequality under nonnegative
weights and observables. Positions do not silently prune: the native indexed
semantics explicitly prunes before constructing its positional presentation.
Likewise positive-support results must not be applied to signed raw lists;
cancellation counterexamples remain tests.

Rational-to-real transport uses `finite_subdist_map_weights` with `ratr`.
It is not an `nnQ` unpack/repack pipeline. Both backends reuse finite bind
construction, but relational lifting, actual joints and semantic equality
remain backend-owned rather than being hidden in the common list layer.

Raw-list equality is the ordinary algebra API. Optional
`FiniteRecordExtensionality` derives checked-record equality using existing
functional extensionality and Boolean-proof equality. Native finite algebra
does not import it; it does not add general proof irrelevance.

## Completion and validation

Finite native carriers are not required to be omega-complete. Generic
`FreeOmega MN` supplies their frontier completion; native laws discharge the
probability-level obligations of generic PTree theory. MathComp is a separate
native self-frontier model, not another specialization of these records.

Current representation, support, inference and behavioral clients live in
Regression; external soundness is summarized in
[FreeOmega soundness](FREEOMEGA_SOUNDNESS.md). Compiled signatures, logical
assumptions and ownership are checked by the maintained commands in
[AUDITING](AUDITING.md).

Completed rename, representation and client-migration stage reports have been
consolidated here. Their exact-source certificates and historical validation
logs are recoverable from Git (including the pre-document-cleanup `1e925b2`).
Those historical replay commands are not current verification requirements.
