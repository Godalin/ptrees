# Maintained verification

The default checks verify the **current tree**, not the sequence of migrations
that produced it. They work with a depth-one checkout. Source-only checks also
work in an archive with no `.git`. Do not add a new `previous_sources` chain or
require old Git objects when introducing another theorem.

See [Examples and tests](REGRESSION_ORGANIZATION.md) for current content
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

## What is deliberately retired

Accepted rename/representation/owner-migration audits, byte-for-byte freezes
of entire earlier libraries, inverse namespace replays, and their Python
mutation tests are no longer daily invariants. They remain recoverable from
Git at their accepted checkpoints (the complete pre-cleanup tools are at
`de66a85`). Superseded stage reports are consolidated into current guides;
their historical text and validation records remain recoverable from Git.

This does not delete mathematical examples or permit new probability
axioms. Runtime tests for replay, lost mass, timeout, errors, State rewriting,
unbounded retry and Bernoulli factory execution remain active.

Proof tactics and helper names are not generally frozen. Valid refactoring
should be checked by compilation, declared boundaries, compiled signatures,
assumptions and real clients rather than an old textual proof recipe.

### Documentation reconciliation

The documentation cleanup after `57c944b` reconciles the root theory status
and README with the proved `from_itree_eutt_reflect` / `from_itree_eutt_iff`
endpoints. Conservativity holds on embedded ITrees under explicit separation
laws; arbitrary-handler reflection and reconstruction of every Prob-free
PTree remain outside that claim. The focused account is
[ITree preservation and reflection](ITREE_PRESERVATION.md).

Topic guides now point to their registered `audit_contracts.py --group ...`
checks instead of deleted stage-specific Python scripts. Obsolete source-replay
instructions, pending-stage statements and old validation-count summaries
are removed from the affected verification sections; the original records
remain recoverable from Git. This is documentation maintenance, not a new
theory result or a rerun of every historical validation campaign. No Rocq
source, snapshot, audit implementation, toolchain or trust policy changes.

For this documentation-only reconciliation, the 56-entry `itree_preservation`
compiled type/assumption group was rerun successfully. Relative documentation
links, referenced audit scripts and contract-group names in the changed guides
were checked against the current files/registry, and `git diff --check` passed.
No full build, new kernel audit or remote CI run is claimed for this change.

## Python cleanup (after `9c807e0`)

Python checks trust boundaries and executable behavior, not how a mathematical
proof is written. Technical tests remain outside the installed theory. The root
`dune build` checks the actual Rocq import, notation, inference and rewriting
clients in `tests/`; Python does not reimplement those elaboration checks.

The following is a review ledger, not another executable migration audit:

| Previous check | Disposition and remaining evidence |
| --- | --- |
| Factory proof must use five named lemmas, exact `unfold`/`setoid_rewrite`, and no `apply`/`eapply` | Removed. Compilation and existing endpoint contracts check the theorem; presentation quality is reviewed, not parsed. |
| Factory helper names, module order, local hypothesis spelling, exact Proper registrations | Removed. Public rewriting clients compile in `tests/Rewriting`; ordinary helper refactoring is allowed. |
| Adaptive/BoundedFactory source substrings | Removed. Backend choice and proof reuse are source-review concerns; this cleanup does not modify either example. |
| Q/R joint bridges must call particular helpers and must not use `induction`/`elim`; compatibility must not contain recursion | Removed. Existing compiled types/assumptions, the inadmissible-intermediate example, and external-validation dependency boundaries remain. No tactic is a soundness criterion. |
| Countable-support file must not mention qlift constructors; backend hitting file must contain particular names | Removed. Mathematical endpoint contracts and compiled clients remain; helper vocabulary is not frozen. |
| Historical reconciliation ledger checked on every test run | Removed. The old reconciliation ledger is retained in Git, not as a current-tree invariant. |
| Five extracted-program test files | Consolidated into `test_execution.py`, sharing one subprocess driver. All 38 actual runtime tests remain. |
| Three source-text extraction-wiring checks | Replaced by one safety check over all four extraction targets: no custom constant/inductive overrides, integer remapping, checker bypass, unrealized extracted axioms or `Obj.magic` in handwritten drivers. The Rocq glue compiles; exact root/helper spellings and OCaml formatting are not frozen. |

Retained Python responsibilities:

- architecture and one-way dependency boundaries;
- unfinished proofs, reviewed capability declarations, logical-axiom policies
  and the exact two-file Gate M allowlist;
- canonical routing/registration and exported notation ownership;
- compiled contracts, their distinct safe/unchecked loading contexts, and
  parser failure-mode tests;
- actual OCaml execution: replay, fuel, entropy errors, lost mass, nested retry,
  interactivity and interruptible divergence;
- CI environment checks, unchanged (no remote CI run is implied).

Minimal public-client import/registration restrictions remain intentional:
they prevent an inference test from silently acquiring extra instances or
implementation imports. Likewise, independence checks on the external model
remain mathematical trust boundaries, not proof-style requirements.

No Rocq source, contract snapshot, class policy, axiom whitelist or toolchain
configuration changes in this cleanup. In particular the snapshot inventory
has **not** been pruned or refreshed to make checks pass. Selecting a smaller
set of frozen helper contracts is separate work requiring endpoint-by-endpoint
review, not part of removing proof-text tests.

The five old runtime test files are removed from the working tree; their full
contents remain recoverable at `9c807e0`. Focused execution checks now use:

```sh
python3 -m unittest discover -s tools -p test_execution.py -v
```

Size changes: 21 → 17 Python files, 2993 → 2800 lines, 149 → 140 tests.
The runtime inventory was compared against `9c807e0`: all 38 runtime test
identities remain; 37 bodies are AST-identical modulo shared-driver names,
and the remaining invalid-input test delegates the same exit-code assertion
to the shared driver. The new extraction-safety test is additional.

Local validation: root `opam exec -- dune build`, all 140 Python tests,
architecture/report agreement, API surface, source safety and all 34 contract
groups' metadata passed. Focused compiled checks passed for
`runner_distribution` (28 entries) and `factory_controller` (47 entries).
The runtime suite was rerun after extending the driver safety check (39 tests
passed). No full compiled-inventory rerun, new kernel audit or remote CI check
is claimed for this Python/documentation-only change.

## Scope of kernel checking

`--kernel` checks selected safe module bodies together, including AllImports,
public/import-order regressions and the new direct iteration modules. It uses
`coqchk -norec`: dependencies are trusted. This is neither the deferred recursive
whole-library audit nor a kernel certification of Gate M's collapsed universes.

## Retired documentation and historical ledgers

Documentation cleanup from `891932f` removes four superseded stage reports:

| Retired report | Maintained account |
| --- | --- |
| Distribution reorganization checkpoints | [Finite backends](FINITE_BACKEND_CONSOLIDATION.md), [FreeOmega soundness](FREEOMEGA_SOUNDNESS.md) |
| MathComp native-only scope / native-order increment | [MathComp](MATHCOMP.md) |
| Case-study refactor log | [Case-study standard](CASE_STUDY_STANDARD.md), [case guide](CASE_STUDIES.md) |

Eight historical JSON files (reconciliation, relocation, before-snapshots and
contract-change ledgers) are also retired. None is a registered contract suite
or read by a maintained tool. All registered `*CONTRACTS.json` snapshots,
`CONTRACT_SUITES.json`, `CONTRACT_POLICY.json` and the generated architecture
inventory are retained unchanged. Stage tails in maintained topic guides are
removed where they describe completed work as pending or repeat old counts.

All removed files can be recovered with `git show 891932f:docs/<filename>`.
The reclassification policy and its original checkpoint summary remain in
[Examples and compilation tests](REGRESSION_ORGANIZATION.md); the detailed
move ledger stays in Git. Source-file changes only redirect example-header
documentation links to the maintained case guide. No theorem, definition,
assumption policy, tool implementation or environment changes.

Local checks for this cleanup: all relative Markdown links in `docs/` resolve;
named audit scripts exist; the 34-group registry metadata check, architecture,
API-surface and source-soundness checks pass, as do 11 contract-tool tests.
Every Rocq edit was compared against the baseline and is exactly a header-link
replacement. `git diff --check` passes. No full build, compiled-theorem audit,
kernel check or remote CI run is claimed for this documentation-only change.
