# Rational shared representation: Phase 4a certificate

Baseline: accepted Phase 3, `683d3c7`.

**Phase 4 remains open.** This increment proves the representation-preservation
obligations before the production rational carrier switch. It does not claim
that `EnumQ` is already `FiniteEnum rat`, or that `SubEnumQ` is already
`FiniteSubdist rat`.

## Why isolate this checkpoint?

The real migration replaced an independently implemented bounded record.
The rational migration additionally replaces a scalar subtype and the list
carrier used directly by indexed coupling, list induction, support and native
observation proofs. A mere renaming of their types would not establish that
their positional semantics survives.

The new `Regression/Backend/RationalRepresentationMigration.v` is a migration
certificate, not a runtime adapter or a new backend. All conversions stay in
Regression, with no coercion, instance, facade export or library consumer.
Nothing is added to the generic probability interface or shared finite algebra.

## Checked correspondence

`rational_shared` sends the old `list (nnQ * A)` to `FiniteEnum rat A` by
projecting each scalar with `Qval`. Its single container invariant is proved
from the original scalar invariants.

`rational_unshare` reconstructs old scalar certificates from the shared
container invariant. This is a constructive recursive operation; it needs no
choice of support, normalization, equality on `A`, or proof-irrelevance axiom.

The two round trips are:

```text
unshare (shared old) = old
raw (shared (unshare new)) = raw new
```

The second equality deliberately compares raw data, not record proofs.
Corresponding bounded conversions have the same two raw-projection round
trips. Their mass obligations follow from exact expectation preservation.

Checked operations/observations:

| Contract | Strength |
| --- | --- |
| ret / zero / scale / map / bind | Exact equality of raw projected lists |
| indexed lookup | Same position; only the scalar projection changes |
| finite AE | Iff with the ordinary-rational nonzero-weight support condition |
| expectation | Equality for **every** rational-valued observable |
| total mass and subprobability | Equality of mass; iff for the bound |
| bounded ret / zero / bind | Exact equality of raw projected lists |

These claims preserve order, repeated values and zero entries, not just
extensional expectation. Regression includes duplicate/zero entries,
overweight unrestricted enumerations, half mass, a null branch, the empty
carrier and a high-universe carrier. No large-carrier equality structure is
assumed.

## Preservation gate

`tools/audit_rational_migration_certificate.py` reads the accepted baseline
directly from Git. It requires:

- every old tracked file unchanged, except exactly the new AllImports import,
  the new regression's contract registration and the generated architecture
  report;
- exactly one new theory module;
- no compatibility coercion/instance, new assumption or checker relaxation in
  the certificate;
- no other module consuming the certificate, except AllImports;
- all 37 new compiled constants closed under the global context.

The old 505-entry contract snapshot is not refreshed. The 161-entry SubEnumR
snapshot, old phase audit tools, all backend source and every DS proof remain
byte-for-byte unchanged. Earlier phase audits remain historical checkpoint
audits; their scope is not weakened to accept this new phase.

## Validation

Local checks for this increment:

```sh
opam exec -- dune build
python3 -m unittest discover -s tools -p 'test_*.py'
python3 tools/audit_architecture.py --check
opam exec -- python3 tools/audit_rational_migration_certificate.py
opam exec -- python3 tools/audit_assumptions.py --check
opam exec -- python3 tools/audit_soundness.py --check
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Prob.Backend.Common.FiniteEnum \
  -norec PTree.Prob.Backend.Common.FiniteSubdist \
  -norec PTree.Regression.Backend.RationalRepresentationMigration \
  -norec PTree.Regression.Infrastructure.AllImports
```

All commands above passed locally: full build, 98 tool tests, architecture,
the certificate audit, all 505 exact compiled contracts, soundness auditing
(199 frozen contracts + 36 generic quotient + 18 finite-real joint + 80 native
MathComp endpoints) and the four-module joint kernel check. All 37 migration
constants are closed under the global context.

The four-module joint kernel command checks those module bodies while trusting
their dependencies (`-norec`); it is not a whole-library recursive audit.
The unchanged two Gate M files are excluded. Ordinary `dune build` continues
to include them and is not described as a wholly universe-checked build.
CI is intentionally not queried or modified.

Counts: 280 -> 281 theory modules; 73 -> 74 Regression modules; 278 -> 279
Gate S modules; 2 -> 2 Gate M modules.

## Remaining Phase 4 work

Replace the production `EnumQ` / `SubEnumQ` definitions and migrate their
list-/index-/support-dependent clients. Reuse the shared finite algebra for
ordinary `rat` coefficients; do not keep these regression conversions as a
permanent execution layer. Preserve native equality/AE/lifting, FreeOmega and
external validation strength with a separate carrier-switch preservation gate.

This certificate alone does **not** establish that those clients have been
migrated, nor that a new rational coupling implementation is equivalent to the
old indexed implementation. No such new implementation is introduced here.
Do not deprecate `nnQ` before its maintained clients are actually migrated.
