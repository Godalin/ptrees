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
| Compiled contracts | `audit_contracts.py` (query helpers: `audit_assumptions.py`, `audit_mathcomp.py`) | types, per-endpoint assumptions, safe/unchecked loading contexts and unsafe-hierarchy reports |
| Examples/tests/kernel | Rocq examples and root `tests/`, `test_*.py`, `audit_api.py --kernel` | mathematical examples/counterexamples, isolated compilation clients, tool failure modes, extracted program behavior, selected joint kernel checks |

The source-level class check normalizes only the eight standard Coq Utf8
logical spellings (`∀ ∃ → ↔ ∧ ∨ ¬ ≠`) to their ASCII counterparts, and
`fun binders => body` to standard `λ binders, body`. Lambda normalization
preserves nested binders, bodies and match-branch arrows. It still
compares every field and premise; compiled type/assumption snapshots are
unchanged and compared exactly.

## Commands

Before building (no installed Rocq or Git history needed):

```sh
python3 tools/audit_architecture.py --aggregate-only
python3 tools/audit_api.py
python3 tools/audit_soundness.py
python3 tools/audit_contracts.py --metadata-only
```

Full local validation with the existing toolchain:

```sh
opam exec -- dune build
python3 tools/audit_architecture.py
python3 -m unittest discover -s tools -p 'test_*.py'
python3 -u tools/audit_contracts.py --gate S
python3 -u tools/audit_contracts.py --gate M
python3 tools/audit_api.py --kernel
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

The historical field `session_collapsed_universes` records whether Rocq
printed the collapsed-hierarchy warning in that endpoint's assumptions block.
An axiom-free safe control may omit it even in the Gate M session; this does
not make the session universe-checked. Absence is accepted only for safe
controls with no logical axioms or unsafe declaration flag. Actual Gate M
declarations must retain both the unsafe flag and the warning. Exact snapshot
comparison still checks every field.

Every expected type and assumptions block is compared exactly in its original
context. The existing soundness whitelist is unchanged. Older mainline
choice dependencies outside that narrower whitelist are listed per endpoint
in the registry, not made generally available to new proofs. Unknown axioms,
malformed output, missing markers and Coq errors with exit status zero fail.

The runner also executes native MathComp, real-joint, generic quotient and
stable-hitting mathematical checks in safe sessions. The protocol-only uniformity negative test still
requires an actual universe-inconsistency diagnostic; the direct-machine
full-interface and fold clients are positive contracts in the safe joint
context. Minimal-import and import-order tests remain actual Rocq modules.

There is only one compiled-contract command: `audit_contracts.py`.
Its query/parser helpers are not standalone audits. Focused mathematical checks
use `--group mathcomp-native`, `--group real-joint`,
`--group generic-quotient` or `--group stable-hitting`; they check additional
signature restrictions, not stored type equality. The complete Gate S run
includes all four, including automatic Q/R stable-hitting modelability.

Optional `--build --gate S` builds only safe targets before checking;
`--build --gate M` builds the isolated unchecked targets. This does not change
the meaning of Gate M or replace the source/dependency checks above.

## Logical assumptions and their roles

The source comments mark strong inversion boundaries; this section summarizes
their meaning for the artifact and paper. The authority for a particular
endpoint is its compiled type and `Print Assumptions` contract, not the
presence of an import or tactic. In particular, `dependent destruction` does
not invariably introduce UIP. A result closed under the global context can
still quantify explicit probability-law premises; its concrete instances can
inherit the assumptions used to prove those laws.

| Assumption family | Role in the current development | Boundary |
| --- | --- | --- |
| UIP (`Eqdep.Eq_rect_eq.eq_rect_eq`) | Strong inversion aligns components of dependent event/response or sampling-carrier packages. | `pstrong_vis_inv`, `pstrong_prob_inv`, `head_step_vis_iff`, `head_bisim_vis_iff`, and clients using such inversions; see the qualifications below. |
| Functional extensionality (including `boolp`'s version) | Converts pointwise agreement to equality of function-valued semantic objects or continuations in some proofs. | Distinct from pointwise relational congruence, which need not equate functions; not a sampling-correctness assumption. |
| Excluded middle | Makes classical case distinctions, e.g. whether a label is enabled or a finite observable head exists. | Used in some generic existence/reflection proofs as well as concrete mathematics; not exclusively a backend assumption. |
| Classical/dependent choice and definite/indefinite description | Selects families of semantic witnesses from pointwise existence, or packages a chosen representative. | For example `trans_exists`, `finite_interaction_query_exists` and selected complete frontiers; different from dependent-index inversion. |
| Concrete classical probability infrastructure | Extensionality, propositional extensionality, choice and classical real-number infrastructure inherited from concrete constructions. | Check the instantiated endpoint: MathComp/real analysis and OmegaVal validation can contribute these dependencies, and rational relational constructions can use classical choice too. |

`stable_head_rel_view_intro` and `head_step_vis_label` preserve a dependent
package or an existential response and are closed under the global context.
In contrast, `head_step_vis_iff` asks for the continuation at a *specified*
response. Its current proof uses UIP; `trans_unique`, `peutt_preserves_trans`,
`peutt_trans_bisim` and MDP transition correspondence inherit that dependency.
The encoding-specific `mdp_choose_head_rel_iff` avoids it because `Choose`
has a fixed action carrier. Consequently the rational source-MDP/`peutt`
correspondence can be UIP-free while its `trans_bisim` counterpart is not.

Do **not** summarize the whole remaining UIP footprint as "only transition
comparison." Recorded dependencies also include ITree reflection
(`from_itree_eutt_reflect` and its iff), FreeOmega translation
(`peutt_translate`), `peutt_preserves_finite_interaction_query`, the
`probabilistic_ptree_bind`/`probabilistic_ptree_iter` validity proofs, and
downstream examples. These proofs still use dependent inversions; this
documentation does not assert that each is unavoidable or that each routes
through the four named strong inversion lemmas.

Conversely, the core `peutt` equivalence, generic bind/up-to rules, main
structural composition and iteration laws, and the maintained Factory and
pGCL/RandomWalk paths do not depend on UIP. This says neither that every
theorem in their directories is UIP-free nor that these paths use no other
axioms. For example `peutt_bind` and `peutt_iter_eventful_rel` are closed under
their explicit profiles, whereas `walk_run` retains functional extensionality,
relational choice and dependent unique choice. Source ITree preservation
`from_itree_eutt` uses excluded middle; reflection additionally uses UIP.

External OmegaVal validation stays outside ordinary behavioral reasoning.
Its classical mathematical assumptions are not implicit premises of generic
PTree theorems. Similarly, `MathCompCouplingGluing` is an explicit probability
premise, not a logical axiom hidden in an instance. Gate M's universe-checking
relaxation is a separate trust boundary, not another item in a logical-axiom
whitelist and not made safe by an empty logical-assumptions block.

### Relation to ITree and CTree

ITree documents UIP for its strong `eqit_inv_Vis` and contrasts it with an
axiom-free weak inversion retaining heterogeneous equality; its README also
separates extensionality from classical/choice assumptions.
See the [ITree Axioms section](https://github.com/DeepSpec/InteractionTrees/blob/master/README.md#axioms)
and [Eqit inversion lemmas](https://github.com/DeepSpec/InteractionTrees/blob/master/theories/Eq/Eqit.v).
CTree explicitly identifies `JMeq_eq`-based dependent `Vis`/`Br` inversion in
[CTreeDefinitions.v](https://github.com/vellvm/ctrees/blob/dev/theories/Core/CTreeDefinitions.v#L418)
and [Equ.v](https://github.com/vellvm/ctrees/blob/dev/theories/Eq/Equ.v#L289).
The analogy is the distinction between packaged and fixed-index inversion,
not an assertion that the three libraries have identical assumption sets.

For paper-facing descriptions, say "currently relies on" or "in our
development." Give one short explanation at the inversion boundary and
brief reminders at dependent comparison results; keep the detailed inventory
in the artifact. Do not claim necessity, impossibility of elimination, or
whole-library constructivity. No necessity theorem for these inversions has
been established here. The comparison above concerns the cited source/API
documentation, not a claim about what is absent from the ITree/CTree papers.

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

## Tool simplification (baseline a0afe7c)

The cleanup changes verification tooling, not Rocq theory or accepted compiled
snapshots. All snapshot types, assumptions, loading contexts, axiom exceptions
and the exact Gate M allowlist remain unchanged.

- Remove the overlapping legacy compiled commands. Source checks do not query
  Rocq; the unified contract runner owns both snapshots and the four explicit
  mathematical checks. The latter stay ordinary code, not a new policy language.
- Replace historical endpoint counts with uniqueness, scope membership and
  required endpoint checks. All registered snapshots still run.
- Pure facade checks compare imports, ordered exports and alias targets, not
  whole source text. Minimal-client imports may be regrouped or reordered.
  Canonical routing remains protected by source ownership checks and actual
  definitional-equality/import-order clients; no full canonical-module source
  copy is frozen in the policy.
- Remove the checked-in generated architecture report and its prose-equality
  gate. `python3 tools/audit_architecture.py --inventory` produces the current
  ownership/client table on demand; every actual dependency rule still runs.
- Retain executable-runtime tests and negative/mutation tests. Reject malformed
  audit output, new assumptions, unsafe flags on safe controls and omitted
  mathematical checks. No CI toolchain or Rocq trust boundary changes.

The removed report and legacy commands are recoverable from Git at `a0afe7c`.
Do not restore per-stage audit entry points or generated prose as proof gates.
