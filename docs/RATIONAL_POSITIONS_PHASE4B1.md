# Phase 4b.1: production indexed-client extraction

Baseline: accepted Phase 4a, `7121338`.

**Phase 4 remains OPEN.** This is the first production-client increment of
Phase 4b, not the rational carrier switch. `EnumQ` is still `list (nnQ * A)`
and `SubEnumQ` is still its bounded wrapper. No runtime representation
conversion or alternative native instance has been introduced.

## Production change

`EnumQ/IndexedCoupling.v` now delegates its two positional recursions directly:

```text
index_from              := finite_index_from
value_index_joint_from  := finite_value_index_from
```

Both shared operations are in `Common/FinitePositions.v`. Their raw layer
works for arbitrary coefficient and value types: it neither computes with
coefficients nor assumes an equality/inhabitation/countability structure on
values. Its arithmetic on positions is ordinary natural-number succession.

The checked layer supplies indexing and value/index joints for both
`FiniteEnum R` and `FiniteSubdist R`, using existing invariants. It proves:

- nonnegativity and exact mass preservation;
- exact length and indexed-lookup behavior;
- exact left/right value/index projections;
- expectation preservation for the left projection;
- commutation with arbitrary scalar mapping, including `Qval` in the
  rational migration.

This removes one old-carrier-specific implementation from an actual
production coupling client before changing the carrier it consumes. It is
not merely another unused backend conversion certificate.

## Frozen semantics

The following are unchanged, including their source text:

```text
at_index
indexed_coupling
indexed
coupling / gluing / relational bind definitions
zero pruning
all theorem statements in IndexedCoupling
all other old probability, FreeOmega, Eq, Interp and Semantics files
```

Two existing projection proofs now invoke shared projection theorems. Five
other proofs only adapt unfolding after the recursive constant has moved.
The source audit reconstructs the entire expected client file from the
baseline using those exact replacements; it does not ignore arbitrary proof
changes or normalize away theorem statements.

The historical implementation is additionally tested by two `reflexivity`
endpoints in `Regression/Backend/RationalPositions.v`. Shared indexing retains
duplicate and zero-weight entries in their original slots. **It does not
perform native zero pruning.** The relation still receives exactly the same
indexed distributions as before this extraction.

The shared raw recursion keeps the coefficient type as a section parameter
and the value type as an explicit recursive parameter, matching the old
native recursion after specialization. Merely moving both parameters outside
the fixpoint would preserve its equations but lose this definitional equality.
The regression checks the stronger property, without proof irrelevance.

## Compiled preservation gate

`audit_rational_positions.py` independently replays the frozen
`IndexedCoupling.v` from Git in a fresh Coq session under a fresh module name.
It compares **all 49 declarations** against the current compiled module:

```text
elaborated type
Print Assumptions
```

Only the fresh reference namespace and printer whitespace are normalized.
The two sessions use the same printing/import context with notation printing
disabled. Coq errors, missing markers, changed premises and changed assumptions
fail the check. No post-migration baseline is captured.

All old tracked files remain byte-for-byte frozen except the exact production
extraction, two sorted aggregate imports, new regression registration and the
generated architecture report. All previous compiled snapshots and phase audit
tools remain unchanged. The Phase 4a conversions remain regression-only; no
production import points at that certificate.

## Local validation

Commands:

```sh
opam exec -- dune build
python3 -m unittest discover -s tools -p 'test_*.py'
python3 tools/audit_architecture.py --check
opam exec -- python3 tools/audit_rational_positions.py
opam exec -- python3 tools/audit_assumptions.py --check
opam exec -- python3 tools/audit_soundness.py --check
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Prob.Backend.Common.FinitePositions \
  -norec PTree.Prob.Backend.EnumQ.IndexedCoupling \
  -norec PTree.Prob.Backend.EnumQ.FrontierLift \
  -norec PTree.Prob.Backend.EnumQ.FinitePresentation \
  -norec PTree.Prob.Backend.SubEnumQ.FreeOmega.JointSoundness \
  -norec PTree.Regression.Backend.RationalPositions \
  -norec PTree.Regression.Infrastructure.AllImports
```

All commands above passed locally:

- full build including AllImports;
- 103 tool tests and architecture/report checks;
- exact source conservation and all 49 independently replayed compiled
  indexed declarations;
- all 42 new shared/regression constants closed under the global context;
- 505 existing exact contracts and their per-endpoint assumptions unchanged;
- soundness audit: 199 exact contracts, 36 generic quotient endpoints,
  18 finite-real joint endpoints, 80 native MathComp endpoints;
- the seven-module joint `coqchk -norec` check.

An initial kernel-check attempt started before the full rebuild had produced
`FreeOmegaSoundness.vo` and reported that missing dependency. It was not
counted as passed; the full command was rerun successfully after `dune build`
finished. No checker or environment settings were changed to make it pass.

`coqchk -norec` checks the named bodies while trusting their dependencies, not
a whole-library recursive audit. The two unchanged Gate M files remain outside
the targeted kernel scope. The ordinary full build still includes them; it is
not claimed wholly universe-checked. CI remains ignored.

Counts: 281 -> 283 theory modules; 74 -> 75 Regression modules; 279 -> 281
Gate S modules; 2 -> 2 Gate M modules. The new shared module has 23 constants;
the regression has 19 definitions/examples.

## Remaining work

The production aliases `EnumQ = FiniteEnum rat` and
`SubEnumQ = FiniteSubdist rat` are **not** introduced by this increment.
Scaling, append/filter, atom mass, finite presentation, and their many clients
still need adaptation to ordinary rational coefficients and container-level
nonnegativity. The indexed relation itself must retain its meaning throughout
that work. Do not mark Phase 4 complete or deprecate `nnQ` yet.
