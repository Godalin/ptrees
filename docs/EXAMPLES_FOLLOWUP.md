# Accepted Gate B: Examples namespace follow-up

Baseline: `20e6ff2`. This follow-up is submitted for separate review before
Gate C. The interpretation theory remains frozen through `ec96b90`.

## Scope

- Rename all 15 application modules from `theories/CaseStudies/` to
  `theories/Examples/`, preserving subdirectories and declaration names.
- Update every source import/qualified reference, the sorted AllImports
  inventory, current ownership/client reports, and user-facing paths.
- Preserve the split: Examples demonstrates program proofs; Regression
  checks semantic/API contracts. Examples cannot import Regression, and
  formal library components cannot import Examples.
- Do not introduce an `Events/` hierarchy or new effect definitions.
  Prefer ITree's existing definitions for standard effects. Existing
  example-specific protocol signatures are unchanged.

The [follow-up manifest](examples-moves.json) is separate from the accepted
Gate B manifest. Gate A baselines and historical move records are not
rewritten; old CaseStudies names there describe their actual snapshots.

## FiniteInternal position

> FiniteInternal is auxiliary proof infrastructure for well-founded internal
> compression and related adequacy arguments. It is not part of the canonical
> PTree semantics or public equivalence theory.

Its definitions and proofs are untouched. It remains under Eq/Internal and
is not exposed through the normal public API. The architecture audit checks
the full dependency closure of peutt, Interp and public facades: none loads
Eq/Internal. This is deliberately a statement about the formal mainline,
not about every Stage 1–4 regression module. For example:

```text
Regression/Semantics/InterpExposure
  -> Regression/Probability/CorrelatedSampleAlgebra
  -> Eq/Internal/FreeOmega/FiniteInternalJointReference
```

These fixture imports remain visible in the client inventory. They do not
justify calling every internal branch indispensable. At the FreeOmega
adequacy audit, retain chains needed by final adequacy results, and review
obsolete/regression-only chains for deletion. Gate C may remove obvious
unused assumptions/imports but should not spend effort redesigning this API.

## Conservation and validation

`audit_migration.py` now also compares **every one of the 208 source modules**
directly against `20e6ff2`: only the literal namespace rename and AllImports
sorting are permitted. Unlike the earlier Gate B audit, this follow-up
check does not strip comments, contexts, imports or proof text. No source
module, theorem, example program or effect signature is added or deleted.

The earlier Gate A → Gate B text audit still works through the composed
namespace map. The 25-endpoint compiled type/logical-assumption comparison
is retained; the accepted baseline files and Gate B manifest remain intact.

Checks to run before handoff:

```sh
opam exec -- dune build
python3 tools/check_aggregate.py
python3 tools/audit_architecture.py --check
python3 tools/audit_migration.py
python3 tools/audit_capabilities.py --check --compare-baseline
python3 -m unittest discover -s tools -p test_audit_tools.py
python3 tools/audit_layout.py
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Regression.Infrastructure.AllImports \
  -norec PTree.Regression.Infrastructure.ArchitectureBoundaries
```

All commands above completed successfully locally: the full build,
208-module exact rename check, the retained Gate A/B conservation check,
25 compiled endpoint types/logical assumptions, all 19 audit-tool tests,
the dependency/client reports, and the two-module joint kernel check.
This import/universe kernel check is not the full per-proof Gate D audit.
No remote CI result is asserted.
Pause for acceptance of this follow-up before capability minimization.
