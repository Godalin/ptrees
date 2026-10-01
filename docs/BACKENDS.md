# Probability backends and trust boundaries

The tree has native sampling `MN`; its complete stable frontiers live in `MF`.
Generic theory fixes neither `MN = MF` nor `MF = FreeOmega MN`.
Operations, probability laws and external-model obligations are separate.

| Backend | Native carrier | Complete frontier | Boundary |
| --- | --- | --- | --- |
| Finite rational | `SubEnumQ` | Observable `FreeOmega SubEnumQ` | Normally checked |
| Finite real | `SubEnumR R` | Observable `FreeOmega (SubEnumR R)` | Normally checked |
| MathComp | `MathCompKernelMeasure R` | Same carrier | Native mathematics checked; recursive-frontier assembly is Gate M |

Raw `EnumQ` is a weighted analysis carrier and has a canonical completion route,
but arbitrary EnumQ values need not be subprobabilities. Ordinary probabilistic
programs should use a bounded backend; numerical analysis may use raw weights.

## Shared finite representation

```text
EnumQ A      = FiniteEnum rat A
SubEnumQ A   = FiniteSubdist rat A
SubEnumR R A = FiniteSubdist R A
```

Coefficients are ordinary scalars. FiniteEnum certifies nonnegativity;
FiniteSubdist additionally certifies mass at most one. Shared finite algebra
works over `numDomainType`, without equality/countability/inhabitation of values.
Order, duplicates and zero entries are retained. There is no implicit raw-list
coercion, normalization, or production old/shared conversion layer; `nnQ` is
legacy, not a maintained coefficient representation.

| Common owner | Responsibility |
| --- | --- |
| `FiniteEnum`, `FiniteSubdist`, `FiniteListAlgebra` | Checked operations, raw finite algebra and expectations |
| `FiniteAtoms`, `FiniteSupport` | Atom mass and support, with explicit nonnegative premises |
| `FinitePositions`, `FinitePresentation`, `FiniteIndexedBind` | Position-preserving finite presentations and bind indexing |
| `FinitePruning` | Stable deletion without aggregation; zero-pruning preserves signed expectations |
| `FiniteScalarMap` | Weight transport; rational-to-real mapping uses `ratr` |

Positions count zero entries; pruning removes them explicitly before indexed
coupling. Arbitrary pruning is only expectation-monotone for nonnegative tests
and weights. Raw-list equality is the ordinary algebra API. Optional
`FiniteRecordExtensionality` proves checked-record equality using existing
extensionality/Boolean-proof facts; native finite algebra does not import it.
Concrete lifting and semantic equality remain backend-owned.

## Finite-real relational mathematics

SubEnumR lifting uses an actual finite joint. Gluing two joints over a common
middle marginal gives matching entries weight `p*q/atom_mass(b)` and all other
entries zero. Cancellation is used only on positive fibers. Duplicate values,
zero entries and deficient mass are supported; no transport-existence axiom,
decidable equality or mass-one premise is added.

Relational bind chooses the supplied continuation joint on related pairs and
zero off the input joint's AE support. The resulting Core/Bind/AELift/CouplingAE
laws instantiate the **existing generic FreeOmega theory**, including actual
`pstruct/pstrong -> peutt`, eventful bind, stable-hitting existence and iter laws.
The finite native carrier itself is not claimed omega-complete.

The independent native expectation interpretations of both Q and R discharge
the same compatibility obligations. Their completion has automatic complete
hitting modelability, countable support and external joint realization; see
[FreeOmega soundness](FREEOMEGA_SOUNDNESS.md). These results are validation,
not prerequisites of ordinary behavioral proofs. SubEnumR native reflection
has a separate explicit validation-side certificate; see [MDP](MDP.md).

## MathComp mathematics and assumptions

There is **no MathComp + FreeOmega backend**. The native model uses discrete /
powerset measurable carriers, not a general continuous/Borel probability
backend. Discreteness does not by itself prove countable support.

| Native owner | Proved mathematics |
| --- | --- |
| `OrderLaws` | Returned-event order and source-bind monotonicity |
| `OmegaLaws` | Increasing-chain lub existence, bind continuity, diagonal/Fubini and omega AE |
| `BindLaws` | Actual joint-kernel bind and mixed relational bind |
| `BindOrder` | Order compatibility, directed cofinality and increasing-lub selection |
| `Retry`, `Iteration` | Positive-success retry cancellation and genuine native least fixed points |

Native order compares returned events, not arbitrary events containing
`MCBottom`. Source-bind monotonicity uses nonnegative integrands vanishing at
bottom, so increasing return mass does not wrongly require increasing cemetery
mass. OmegaLaws constructs actual measures from increasing returned-event
suprema; it does not assume lub existence. Continuity and diagonal cofinality
justify simultaneous source/continuation limits.

Joint-kernel bind selects existing joints on related inputs, integrates them
against the input joint, and proves projections/support. This does not prove
general gluing. `MathCompCouplingGluing R` remains an explicit premise of
relational composition/CoreLaws. Unrestricted relational-lub also remains open:
countable external limits and a supplied increasing joint chain give separate
sufficient results, not an unconditional native theorem. See [Theory](THEORY.md).

## Gate M: exact local relaxation

Only these files may contain one `Local Unset Universe Checking.`:

- [`Eq/Backend/MathComp.v`](../theories/Eq/Backend/MathComp.v)
- [`tests/MathComp.v`](../tests/MathComp.v)

The former assembles `MN = MF` for `mathcomp_tree`, `mathcomp_frontier`,
`mathcomp_kernel`, `mathcomp_hitting`, `mathcomp_peutt` and their generic theorem
specializations. The latter checks unbounded retry, eventful bind/Vis, nested
retry with diagonal limits, MDP correspondence and conditional stronger algebra.
No MathComp-specific copy of generic PTree coinduction is used.

Every other module is Gate S and must not depend directly or transitively on
Gate M. The safe aggregate excludes both files. Checked negative native-universe
probes remain alongside the explicitly relaxed assembly; compiling both does
not resolve the universe inconsistency. Native probability proofs stay checked.

The Gate M audit records per-declaration unsafe-hierarchy flags and the collapsed
session warning separately from logical axioms. Safe controls must stay untainted.
An ordinary full build includes Gate M and is **not** a universe-checked
whole-library result. No further file inherits a bypass from its directory.

## Checking a model

Use the actual generic theorem's profile rather than requiring every backend
to satisfy every optional law. Concrete assumptions are recorded per endpoint.
Normally checked gluing-free native results must not be described as having the
same assumptions as their CoreLaws-based PTree consumers. The [verification
guide](AUDITING.md) gives the safe and Gate M commands; the [architecture
guide](ARCHITECTURE.md) fixes one-way external-model dependencies.
