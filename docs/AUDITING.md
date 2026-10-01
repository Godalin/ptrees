# Maintained verification

The default checks verify the **current tree**, not the sequence of migrations
that produced it. They work with a depth-one checkout. Source-only checks also
work in an archive with no `.git`. Do not add a new `previous_sources` chain or
require old Git objects when introducing another theorem.

See [Examples and tests](ARCHITECTURE.md#examples-and-tests) for current content
roles and retention/deduplication criteria. Snapshots complement actual
clients; they do not replace inference, rewriting or import-order tests.

## Four responsibilities

| Responsibility | Tools | What is checked |
| --- | --- | --- |
| Architecture | `audit_architecture.py` | actual dependency edges, ownership, aggregate coverage, external-model and Gate M isolation |
| Safety/public surface | `audit_soundness.py`, `audit_api.py`, `mathcomp_policy.py` | unfinished proofs/assumptions, reviewed class declarations, exact bypass allowlist, routing registrations and notation owners |
| Compiled contracts | `audit_contracts.py`, `audit_assumptions.py`, `audit_mathcomp.py` | types, per-endpoint assumptions, safe/unchecked loading contexts and unsafe-hierarchy reports |
| Examples/tests/kernel | Rocq examples and root `tests/`, `test_*.py`, `audit_api.py --kernel` | mathematical examples/counterexamples, isolated compilation clients, tool failure modes, extracted program behavior, selected joint kernel checks |

## Commands

Before building (no installed Rocq or Git history needed):

```sh
python3 tools/audit_architecture.py --aggregate-only
python3 tools/audit_api.py --surface-only
python3 tools/audit_soundness.py --source-only
python3 tools/audit_contracts.py --metadata-only
```

Full local validation with the existing toolchain:

```sh
opam exec -- dune build
python3 tools/audit_architecture.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
python3 -u tools/audit_contracts.py --gate S
python3 -u tools/audit_contracts.py --gate M
python3 tools/audit_api.py --surface-only --kernel
```

The root build includes `theories/` (`PTree`) and `tests/` (`PTree.Tests`).
It compiles `Fail` probes in their own import contexts as well as safe AllImports.
`tools/rocq_paths.py` centralizes both roots and their load paths for audits;
there is no additional test-only Rocq build step.

Do not run the CI bootstrap in a working local switch. Compiler, opam and
dependency pins are unchanged. The environment checker remains CI-specific.

For a focused iteration, use `audit_contracts.py --group direct_iteration`
(or another id in `tools/data/CONTRACT_SUITES.json`). CI runs every group; a focused local
check is not a claim that the whole verification suite passed.

## Contract data and trust contexts

[`tools/data/CONTRACT_SUITES.json`](../tools/data/CONTRACT_SUITES.json) is the single registry. Existing snapshots remain data
files, preserving reviewed type/assumption strings and their useful thematic
groupings; no separate executable audit is needed per stage. New unregistered
snapshot files or an omitted embedded `direct` group fail inventory validation.
There is no automatic snapshot-update mode.

The runner preserves five explicit contexts:

- `owners`: import the endpoint owners, as in the original check;
- `recorded`: use the central snapshot's recorded module set;
- `safe-joint`: query after safe AllImports (essential for full uniformity);
- `gate-m-joint`: safe AllImports, then an isolated relaxed-checking session;
- `gate-m`: the already-reviewed direct-client session without the aggregate.

Repeated endpoints in different contexts are intentional. They must not be
deduplicated into one global session: doing so could erase a universe/import
boundary or contaminate safe validation with unchecked MathComp imports.
Gate M results never count as universe-checked evidence. Its declaration flags
and session warnings remain separate from logical axioms; safe controls must
remain untainted. The allowed set of Gate M source files is still exactly two:
`theories/Eq/Backend/MathComp.v` and `tests/MathComp.v`.

Every expected type and assumptions block is compared exactly in its original
context. The existing soundness whitelist is unchanged. Older mainline
choice dependencies outside that narrower whitelist are listed per endpoint
in the registry, not made generally available to new proofs. Unknown axioms,
malformed output, missing markers and Coq errors with exit status zero fail.

The runner also executes the existing native MathComp, real-joint and generic
quotient mathematical checks. The protocol-only uniformity negative test still
requires an actual universe-inconsistency diagnostic; the direct-machine
full-interface and fold clients are positive contracts in the safe joint
context. Minimal-import and import-order tests remain actual Rocq modules.

`audit_assumptions.py` and `audit_api.py` still support their focused legacy
commands, but checking only the central manifest is **not** a full run of
the extended contract inventory.

## Trust and kernel checks

A full build includes the two Gate M files and is not a universe-checked
whole-library result. Safe AllImports checks joint universe compatibility of
all Gate S modules. `audit_api.py --kernel` rechecks selected safe module bodies
jointly with `coqchk -norec`; dependencies are trusted, not recursively rechecked.
Repeat `-norec` for each manually selected target. This is not the deferred
whole-library kernel audit, nor a consistency result for collapsed Gate M
universes. See [backend boundaries](BACKENDS.md#gate-m-exact-local-relaxation).

## Maintenance policy

Validate the current tree, not historical migration scripts. Keep mathematical
examples and concrete elaboration/rewrite clients; do not freeze proof tactics,
local helper names, line counts or exact rewrite scripts in Python. No snapshot
is automatically refreshed to make a failing comparison pass. New assumptions
or changed contracts need explicit review.

There is one current guide per reader task, indexed in [README](README.md).
Do not add another report for each feature, commit or acceptance checkpoint.
Historical proposals, intermediate limitations, acceptance counts and migration
ledgers remain in Git. For the pre-consolidation documents use
`git show 2ba1855:docs/<filename>`.

The consolidation from `2ba1855` reduces 50 narrative/generated Markdown files
to 12 maintained guides. All 31 JSON data files and the generated architecture
inventory move to `tools/data/`. Snapshot/policy/inventory bytes are preserved;
only registry snapshot paths and tool locations change. Existing safe/unchecked
query contexts, per-endpoint axiom exceptions and test coverage remain intact.
Source-file edits are documentation references only, not theorem changes.
