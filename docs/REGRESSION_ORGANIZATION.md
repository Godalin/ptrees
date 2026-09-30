# Regression policy

Regression tests protect observable boundaries, elaboration and integration.
They are not a second theorem library or a permanent archive of development
stages. Historical migration certificates and validation logs belong in Git.

## Keep a test when it checks a distinct failure mode

- Negative semantic boundaries: invalid raw limits, missing mass, escaping
  mass, strictness and interpreter-exposure counterexamples.
- Actual clients: rewriting under constructors/continuations, heterogeneous
  relations, mixed or infinite programs, and backend assembly.
- Minimal capabilities/imports, canonical routing under different import
  orders, high-universe carriers and the isolated MathComp checker boundary.
- Execution distinctions: semantic loss, fuel exhaustion and entropy exhaustion.

A parameterized lemma that only applies an already audited theorem is normally
redundant. Keep it only when its deliberately weak signature or isolated import
context is itself the contract. A substantive reusable mathematical law belongs
at its production owner; a readable application belongs in Examples. Do not
move disposable tests there just to reduce the regression count.

## Ownership

| Directory | Responsibility |
|---|---|
| Backend | Native representations, capability inference and actual backend clients |
| Probability | Independent domain, transport, limit and quotient boundaries |
| Semantics | Rewriting/handler/transition clients and semantic counterexamples |
| Execution | Runner, replay and resource-failure tests |
| Infrastructure | Public surface, aggregate, universe and capability boundaries |
| ImportOrder | Independently compiled canonical-routing probes |
| Internal | Clients of maintained auxiliary scheduling/compression/recovery theory |
| Fixtures | Shared test data, never a public theory dependency |

Import-order and negative-import probes must execute before the competing
imports are loaded. Do not merge independent sessions merely to reduce files.
MathComp Gate M stays in its exact file allowlist and outside safe AllImports.
Retiring an internal regression does not authorize deleting its production
FiniteInternal/Recovery infrastructure.

## One generic contract, representative concrete clients

Do not reproduce every algebra law for every backend. Test the generic theorem
with its intended capability context; then retain concrete clients that exercise
the whole composition. Similarly, test generic completion capabilities once and
native capabilities separately, with actual Q/R PTree clients checking assembly.

For finite lists, current shared operations and concrete examples pin order,
duplicate entries, zero weights, signed observations, partial mass and scalar
transport. Copies of historical recursive implementations are not required once
the representation migration is accepted.

For external soundness, retain actual joints through inadmissible composition
middles, partial mass and large carriers. Repeating the same invalidity theorem
under several stage-local names adds no coverage.

## Current consolidation

The current pass starts from `ebce8e0`; it changes no production Rocq source.
It removes redundant proofs rather than merging independent test contexts.

| Area | Retained responsibility / removed duplication |
|---|---|
| Finite sampling | Retire HittingPrograms and its private nested/flattened fixtures; retain native split/reorder coupling, UnifiedFrontierEnumQ's universe client, PEuttAlgebra rewriting and nonuniform Tau/visible-head hitting computations |
| StableHittingDomain | Audit arbitrary-witness modelability/adequacy at the generic and Q/R production owners; retain changing silent loops, visible-service mass, native loss, noncanonical witnesses and real-weight recursive clients |
| KleisliIteration | Retain endless-retry leastness and native-loop interpretation; remove redeclarations of fixed-point, existence and leastness laws already audited at production owners |
| MDPEncoding | Remove generic iff wrappers; retain infinite counter encodings and concrete positive/negative labelled-probability pairs for both peutt and trans_bisim |
| RelationalLimit | Retain the stronger no-coherent-joint-selection counterexample and actual limit existence; remove its weaker fixed-initial-joint variant and a direct equality-law wrapper |
| SubEnumRJointRealization | Retain real retry with exact marginal/mass/support evidence, partial mass, invalid raw enumerable terms and heterogeneous large carriers; remove weaker existence and self-equality wrappers |
| MathCompOrder / MathCompOmega | Retain capability inference, isolated-import boundaries, cemetery/partial-mass cases, null branches and relational bind; remove repeated generic law applications |
| FiniteSupport / TreeTransitionSoundness | Retain cancellation/function/high-universe boundaries and actual action/heterogeneous clients; remove elementary atom facts and wrappers around existing examples |

Nothing is relocated into Examples or production to obtain these reductions.
The removed file and declarations remain recoverable from Git. This is a review
of these clients, not a claim that every remaining regression is irreducible.

Regression sources decrease from 103 files / 16,762 lines to 102 files / 16,269
lines. The whole theory has 433 modules, including the unchanged two Gate M
modules. File count is a consequence, not the acceptance criterion.

## Contract snapshots and validation

Freeze production endpoint types and logical assumptions. Snapshot a regression
signature when its capability or universe shape is the contract, not every
helper distribution, proof step or phase-local wrapper. Building an actual
rewrite test is still necessary: a stored Proper signature cannot replace it.

This pass removes only retired regression snapshot/policy entries and their
now-unreferenced per-endpoint axiom registrations. Production entries, surviving
axiom whitelists and Gate M snapshots stay unchanged.
No snapshot is regenerated from current output to hide a mismatch.

Use the existing verification tools in [AUDITING.md](AUDITING.md). No additional
historical-replay checker or per-cleanup audit framework is introduced. Validate
changed clients and AllImports, source/architecture/API policies, tool tests,
affected compiled contract groups and a clearly scoped kernel check.

Local checks for this pass passed:

- Full `dune build`, including AllImports and extraction targets; 148 Python tests.
- Architecture, API surface, source soundness and contract-metadata checks.
- Exact compiled suites: `relational_limit` 20, `subenumr_migration` 122 and
  `mdp_correspondence` 6 entries.
- Soundness queries: 76 MathComp native, 27 hitting/Q/R and 16 finite-real
  joint endpoints, with the existing logical-axiom whitelist.
- Snapshot comparison against `ebce8e0`: only six retired regression entries
  removed; every other entry and every surviving axiom registration unchanged.
- Joint `coqchk -norec` for MDPEncoding, RelationalLimit,
  StableHittingComputation, StableHittingDomain, MathCompOmega and
  SubEnumRJointRealization. Dependencies were trusted; this is not a recursive
  whole-library audit. Native conversion fell back to VM conversion.

CI was not queried. No new audit framework or environment changes were needed.
