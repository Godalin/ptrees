# Maintained verification

The default checks verify the **current tree**, not the sequence of migrations
that produced it. They work with a depth-one checkout. Source-only checks also
work in an archive with no `.git`. Do not add a new `previous_sources` chain or
require old Git objects when introducing another theorem.

## Four responsibilities

| Responsibility | Tools | What is checked |
| --- | --- | --- |
| Architecture | `audit_architecture.py` | actual dependency edges, ownership, aggregate coverage, external-model and Gate M isolation |
| Safety/public surface | `audit_soundness.py`, `audit_api.py`, `mathcomp_direct_policy.py` | unfinished proofs/assumptions, reviewed class declarations, exact bypass allowlist, routing registrations and notation owners |
| Compiled contracts | `audit_contracts.py`, `audit_assumptions.py`, `audit_mathcomp_direct.py` | types, per-endpoint assumptions, safe/unchecked loading contexts and unsafe-hierarchy reports |
| Regression/kernel | Rocq modules, `test_*.py`, `audit_api.py --kernel` | real positive/negative clients, tool failure modes, extracted program behavior, selected joint kernel checks |

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

Do not run the CI bootstrap in a working local switch. Compiler, opam and
dependency pins are unchanged. The environment checker remains CI-specific.

For a focused iteration, use `audit_contracts.py --group direct_iteration`
(or another id in `CONTRACT_SUITES.json`). CI runs every group; a focused local
check is not a claim that the whole verification suite passed.

## Contract data and trust contexts

`CONTRACT_SUITES.json` is the single registry. Existing snapshots remain data
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
remain untainted. The allowed set of Gate M **theory files** is still exactly two.

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
commands, but checking only the central 465 entries is **not** a full run of
the extended contract inventory.

## What is deliberately retired

Accepted rename/representation/owner-migration audits, byte-for-byte freezes
of entire earlier libraries, inverse namespace replays, and their Python
mutation tests are no longer daily invariants. They remain recoverable from
Git at their accepted checkpoints (the complete pre-cleanup tools are at
`de66a85`). Old stage reports describe those historical verifications; their
tool commands are not current instructions.

This does not delete mathematical regressions or permit new probability
axioms. All Rocq files and executable implementations are unchanged by this
cleanup. Runtime tests for replay, lost mass, timeout, errors, State rewriting,
unbounded retry and Bernoulli factory execution remain active.

Proof tactics and helper names are not generally frozen. Valid refactoring
should be checked by compilation, declared boundaries, compiled signatures,
assumptions and real clients rather than an old textual proof recipe.

## Scope of kernel checking

`--kernel` checks selected safe module bodies together, including AllImports,
public/import-order regressions and the new direct iteration modules. It uses
`coqchk -norec`: dependencies are trusted. This is neither the deferred recursive
whole-library audit nor a kernel certification of Gate M's collapsed universes.
