# Generic algebra and rewriting

## Current rewriting library

The generic library owns the mathematical proofs. Concrete clients select a
frontier interpretation and register proof-backed `Proper` specializations
locally; they do not reproduce the proofs or introduce congruence axioms.

| Owner / laws | Actual requirements beyond the interpretation operations |
| --- | --- |
| `Eq/Algebra`: `peutt_bind_{ret_l,tau,vis,prob}`, `peutt_fmap_{ret,tau,vis,prob}` | Frontier CoreLaws only; shallow observation equality |
| `Eq/Algebra`: `peutt_sample_bind` | Native/frontier CoreLaws, frontier BindLaws, mixed laws, order/omega/cofinality and mixed omega laws |
| `Eq/Algebra`: `peutt_prob_map`, `peutt_sample_map` | Same sampling profile plus mixed unit and node-bind compatibility |
| `Interp/ExceptionFacts`: `run_exception_peutt_eq_Proper` | Existing exception preservation profile: CoreLaws, order/omega, bind/mixed order, directed cofinality, explicit relational bind |
| `Interp/IterationUniform`: `peutt_iter_Proper` | Existing direct-iteration profile: Core/Bind, order/omega/cofinality/diagonal/Fubini, bind/mixed order, directed selection, explicit relational zero and relational lub |
| `Interp/StatePreservation`: `run_state_peutt_eq_Proper` | Existing generic State preservation theorem (unchanged) |
| `Interp/Unrestricted`: `peutt_interp_Proper` | Existing generic interpretation theorem (unchanged) |

The sampling laws do not require total mass, commutativity, relational-lub
closure, a specific native representation, or a completion type. In particular,
`peutt_prob_map` accepts an arbitrary continuation, not only `Ret`. Their compiled
signatures and assumptions are recorded in `GENERIC_ALGEBRA_CONTRACTS.json`.

The `Rewriting` module of `Examples/FactoryController.v` invokes the generic sampling laws directly
and contains no `Instance`, `Existing Instance` or hints. Its relation is a
local notation for explicitly selected raw `PEutt.peutt`, not `canonical_peutt`.
Embedding, factory and controller congruences are exported by their example
owners because they mention application programs. The complete calculation
now rewrites directly inside the manufacturing step, then rewrites that
pointwise step equality under the handler stack, using library congruences
automatically rather than applying Proper manually;
it is defined before `Facts` and cannot depend on that example's
embedding/controller helpers.

### Opt-in completion registrations

`Interp/FreeOmega/Rewriting.v` contains six registrations of the generic
bind/ProbF/State/interp/exception/iter `Proper` proofs. They are native-parametric, not
copies for EnumQ, SubEnumQ and SubEnumR. Activate them with:

```coq
From PTree.Interp.FreeOmega Require Import Rewriting.
Import FreeOmegaRewriting.
```

The nested module uses `#[export] Instance`, not `#[global]`. Loading the file
without importing the nested module does not enable its hints; neither does an
import inside another client module leak them. The public `PTreeFacts` facade
does not automatically opt in. The support module has no dependency on
`Eq/Canonical`, concrete backends or application programs. It fixes the
observable FreeOmega interpretation and supplies existing probability
certificates, without reproving congruence or making certificates new classes.

The bind registration fixes the observable frontier before typeclass search
resolves its laws. Without it, bind rewriting can repeatedly try completion
instances for an unconstrained frontier. Its proof is the existing generic
`Eq.Algebra.peutt_bind_Proper`, with the interpretation explicitly supplied;
it introduces neither a backend-specific mathematical proof nor a new law.

`tests/Rewriting/FreeOmegaRewriting.v` checks both negative import
boundaries, inferred `Proper` goals for arbitrary native `MN`, actual
bind/source/continuation, sampling and loop rewriting, and SubEnumR/SubEnumQ clients without local instances. The
factory is the EnumQ client, exercising the complete handler/loop stack.
Direct MathComp is intentionally not part of this completion module; its
generic theorems and explicit mathematical premises are unchanged.

### Constructor-context rewriting

`Vis` and `Prob` expand to `go (VisF ...)` and `go (ProbF ...)`. The generic
`Eq/Algebra` instances `peutt_visF_Proper` and `peutt_probF_Proper` connect
pointwise continuation relations to the existing `Shallow.going` relation;
`going_go` then closes the outer context. They reuse existing congruences,
without functional equality of continuations or new probability assumptions.
The optional `free_omega_probF_Proper` fixes the observable interpretation for
this decomposed sampling path, avoiding unconstrained frontier search. It is
an application of the generic theorem, not a separate completion proof.
Generic regressions run before any concrete backend import; the opt-in
regression separately checks actual rewriting under `Prob`.

Sampling wrappers inherit the probability congruence's logical dependencies;
these are recorded per endpoint in `GENERIC_ALGEBRA_CONTRACTS.json`, rather
than hidden by broadening a global whitelist. Historical migration counts
and before/after assumption ledgers remain in Git.

`tests/Rewriting/GenericAlgebra.v` checks the minimal shallow profile,
generic ownership/import isolation, arbitrary-native FreeOmega sampling and
finite-real sampling/loop rewriting. `tests/MathComp.v`
checks the same sampling theorems at `MN = MF`, and iteration `Proper` with an
explicit `relational_lub` premise. This does not discharge MathComp's remaining
relational-limit obligation. Its existing gluing premise and two-file Gate M
boundary are unchanged. No new global instances, classes or hints are added.

The seven new shallow equations and the generic exception/iteration additions
are closed under the global context. The three sampling laws inherit
`eq_rect_eq`, `RelationalChoice.relational_choice` and
`ClassicalUniqueChoice.dependent_unique_choice` from the existing probability
rewriting facts. These dependencies are recorded per endpoint; the global
logical-axiom whitelist is not enlarged. Concrete specializations also inherit
their backend's existing logical dependencies.

Local validation of this extension from `fd2f72c`:

- Full `dune build`, including safe AllImports and the separately labelled
  Gate M modules, passed; this is not a whole-library universe-safety claim.
- 136 tool tests passed. Contract metadata tests were rerun after registering
  the new entries (12 passed).
- All 465 mainline and 22 factory contracts were unchanged. The 18 old generic
  algebra contracts were checked before appending 24 new entries; all 42 safe
  contracts and three new, separately queried Gate M clients passed.
- Architecture, source/capability safety, and public-surface checks passed.
- Joint `coqchk -norec` passed for seven changed safe module bodies. Dependencies
  were trusted; Gate M was excluded. This is not a recursive whole-library audit.
- Extracted `controller.ml` and `controller.mli` hashes are unchanged. No program,
  handler, sampler, extraction implementation or canonical route was changed.
- Remote CI was not queried.

Current reproducible checks use `audit_contracts.py --group generic_algebra`,
`--group generic_algebra_gate_m`, `--group factory_controller`, plus the
normal build, architecture/source checks and tool tests. The scripts and counts
in the historical report below describe that older checkpoint, not today's
audit infrastructure.

## Backend requirements

The generic theorem owners and their actual model obligations are summarized
in [Generic consumers](GENERIC_CONSUMERS.md#current-capability-and-model-status)
and [Generic relational consumers](GENERIC_RELATIONAL_CONSUMERS.md).
The former Stage 1 move plan is no longer a current TODO: subsequent work
established generic structural bridges and elementary algebra under explicit
relational-closure laws. FreeOmega supplies those laws; MathComp clients retain
any still-required gluing/relational-lub premises. The original move plan,
proof-text conservation records and before/after tables remain in Git.

## Current verification

These are focused checks of the current compiled types and logical assumptions:

```sh
python3 tools/audit_contracts.py --group generic_algebra
python3 tools/audit_contracts.py --group generic_algebra_gate_m
```

Build first with `opam exec -- dune build`. For architecture, source safety,
all registered groups, runtime tests and the separately scoped kernel check,
use [Maintained verification](AUDITING.md). Gate M checks are isolated and do
not constitute universe-checked evidence. Local checks do not assert CI passed.
The retired stage-specific source-replay scripts and their historical
module/test counts remain in Git; they are not current-tree invariants.
