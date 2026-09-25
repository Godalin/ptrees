# Current-tree audit consolidation

Baseline: `de66a85` (after the full iteration-uniformity implementation).

## Cause and scope

The inspected failed CI run, `36091686507` at `88e9cf2`, passed compilation,
architecture, source safety and the central compiled contracts. Python tests
then reported 189 errors while reading historical commits absent from the
shallow checkout. Fetching the entire repository would hide that symptom but
leave accepted migration history as a permanent dependency of routine checks.

This cleanup instead checks the current tree. It changes no Rocq source,
extracted implementation, compiler/dependency profile, axiom whitelist or
MathComp checker-relaxation boundary. All 417 theory modules remain intact.

## Reduction

| Item | Before | After |
| --- | ---: | ---: |
| Python files in tools | 84 | 19 |
| Audit scripts | 40 | 6 |
| Audit-script lines | 5858 | 1167 |
| Python test files | 41 | 11 |
| Python tests | 347 | 124 |
| Maximum historical source-replay chain | 20 | 0 |
| Executable/runtime tests | 33 | 33 |

35 historical audit scripts, 31 historical test files and one migration helper
were removed. Their accepted evidence is preserved in Git, including the full
pre-cleanup tools at `de66a85`. No Rocq regression was pruned. The executable
tests still exercise effects, rational tickets, state rewriting, unbounded
execution and factories.

The remaining responsibilities and commands are in [AUDITING.md](AUDITING.md).
There is one compiled-contract runner and one explicit registry. The thematic
JSON snapshots remain data, not per-stage executable audits. Query contexts
are preserved rather than flattened into a single potentially unsafe session.

## Coverage and snapshot reconciliation

The registry runs 24 safe groups (1363 records, 1345 distinct endpoint names)
and five isolated MathComp groups (59 records, 53 distinct names, including
safe controls). It also retains the 80 native MathComp, 18 real-joint and
36 generic quotient mathematical probes and the cause-sensitive negative
uniformity-package check. The 22 generic bind/profile probes formerly computed
by a stage script are now explicit snapshot data.

The central 465-entry snapshot and all existing MathComp snapshots are
unchanged. Enabling every old extension snapshot uncovered seven already-stale
entries in `SUBENUMR_MIGRATION_CONTRACTS.json`: five rational-embedding entries
still used the old owner name, and two behavioral entries retained obsolete
choice dependencies. Three of the embedding entries also retained an obsolete
extensionality dependency. Only these seven entries were reconciled against
the unchanged compiled theory; no premise was added and axiom sets only shrink.

[The reconciliation ledger](AUDIT_CONTRACT_RECONCILIATION.json) records each
exact old/new entry. A test checks owner-normalized type preservation and
non-growth of logical dependencies. There is no automatic snapshot refresh
mode or wider axiom whitelist.

## Local verification

- Full `dune build` and compiled architecture check passed.
- Current source/public-surface/contract-inventory checks passed.
- All 124 Python tests passed (67.346 seconds locally), including all 33 actual
  executable tests and a source-archive test without `.git` or build artifacts.
- A real local `--depth 1` clone also passed all four pre-build checks; its
  history contained exactly one commit and the old baseline object was absent.
  All 91 audit/tool tests passed there too, without compiled artifacts; the
  other 33 executable tests were run in the built working tree above.
- All registered Gate S and Gate M compiled groups passed in their explicit
  query contexts, together with the additional mathematical probes.
- Theory, extraction and fixed-environment paths have no diff from the baseline.

CI deliberately remains shallow and performs fast source checks before
installing dependencies. The local test-time reduction is not a promise of
shorter total CI time: CI now checks the extended contract inventory, rather
than only the central 465 entries. Remote success must be established by the
new workflow run, not inferred from these local results.

The targeted kernel command checks 23 safe module bodies jointly using
`coqchk -norec`; its dependencies are trusted. It is not the deferred recursive
whole-library audit and never certifies Gate M as universe-checked.
The additional local run was manually stopped after approximately 14 minutes
without completion and is **not counted as passed**. The command remains in
CI; the successful build and contract queries are not a substitute for its
kernel-recheck result. This audit-only change modifies no proof source.
