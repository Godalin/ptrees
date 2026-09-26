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

The factory-controller calculation now invokes the generic sampling laws
directly. Its four handler/iter `Proper` declarations are only local
specializations. Embedding, factory and controller congruences remain in their
example owners because they mention application programs.

`Regression/Semantics/GenericAlgebra.v` checks the minimal shallow profile,
generic ownership/import isolation, arbitrary-native FreeOmega sampling and
finite-real sampling/loop rewriting. `Regression/Backend/MathCompDirect.v`
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

## Historical Stage 1 report

This is a historical stage report. For current backend certificates and the
subsequent shallow left-unit premise reduction, see
[the current consumer status](GENERIC_CONSUMERS.md#current-capability-and-model-status).

Baseline: `ad8705f`. This stage moves consumers, not probability foundations.
Stages 2 (structural bridges), 3 (iteration), and 4 (interpretation) require
separate commits and review. They are not claimed here.

## Before/after compiled capability surface

The two old `Eq.FreeOmega.Algebra.peutt_{bind,fmap}_Proper` declarations fixed
`MF := FreeOmega MN`, its observable measure/core/omega instances, and the
FreeOmega mixed bridge. Their actual compiled parameters were native measure
operations, CoreLaws, AELiftLaws, omega operations, CouplingAELaws, and
CountableAELaws. Their global logical dependencies were functional
extensionality and `eq_rect_eq`.

`Eq.Algebra` now owns both declarations and their proofs. They consume the
existing generic `Eq.Bind.peutt_bind`, with exactly its semantic profile:

| Purpose | Capabilities |
| --- | --- |
| Chosen interpretation | frontier `SemanticMeasure`, `MixedMeasure`, `SemanticOmega` |
| Relational algebra | frontier CoreLaws and BindLaws |
| Increasing limits | OrderLaws, OmegaLaws, CofinalityLaws, DiagonalLaws |
| Finite approximation scheduling | BindOrderLaws, MixedMeasureBindOrderLaws, DirectedCofinalityLaws |
| Witness choice | SemanticOmegaSelection |

The compiled generic signatures have no native measure context, FreeOmega or
MathComp carrier, AELift, CountableAE, commutativity, Fubini, or mixed omega
continuity premise. Both proofs are closed under the global context. This is
not a claim that the probability laws themselves are assumption-free: concrete
instances still contribute their own recorded logical dependencies.

The old FreeOmega statements are recovered exactly in
`Regression.Semantics.GenericAlgebra.free_omega_{bind,fmap}_Proper` by applying
the new theorem, not by repeating a backend proof. The audit compares compiled
types modulo the declaration name and printer whitespace, and checks that
assumptions do not grow.

Two additional safe SubEnumR probes instantiate both generic Proper theorems
with `FreeOmega (SubEnumR R)`. Thus the concrete finite-rational, finite-real,
and direct MathComp routes are all exercised, not only an abstract MN section.

`Eq.FreeOmega.Algebra` exports the actual generic owner, with no alias or second
declaration. `PTreeFacts` also exports the generic owner explicitly.

## Rewriting and profile selection

Both FreeOmega and direct MathComp regressions perform actual `setoid_rewrite`
under bind's source, bind's continuation, and fmap. The old EnumQ tests retain
their theorem statements and proof bodies, with two local instance
specializations supplied before the tests.

There is an important inference boundary: the tree carrier determines `MN`,
not `MF/FI/MX/FO`. Bare rewriting with all these parameters unresolved caused
long typeclass backtracking in both concrete clients. The regression therefore
first obtains a local `Proper` fact at the intended relation using the generic
theorem, then rewrites. For a continuation, its pointwise hypothesis is exposed
as `pointwise_relation` before rewriting the function itself. No global hint,
new canonical route, or backend copy of the congruence proof was added.

For example, a public client can use:

```coq
assert (Hp : Proper ((fun a b => a ≈ₚ b) ==>
  pointwise_relation A (fun a b => a ≈ₚ b) ==>
  (fun a b => a ≈ₚ b)) (@PTree.bind E MN A B))
  by apply peutt_bind_Proper.
setoid_rewrite H.
```

The new MathComp tests are in the already allowlisted regression file.
`MathCompCouplingGluing` remains explicit. Gate M is not enlarged and is not
claimed to be universe-checked.

## Derived probability facts, not new requirements

`Prob.Interface.Coupling.coupling_ae_implies_ae_lift` constructs AELiftLaws from
CoreLaws and CouplingAELaws: restrict a reflexive equality coupling to an AE
predicate in both marginals, then weaken its relation. It is an ordinary lemma,
not an automatically registered instance. It is closed under the global context.

`free_omega_observable_dirac_ae_laws` moves, with its statement and proof
byte-for-byte intact, from `Semantics.FreeOmega.MDPCoincidenceFreeOmega` to
`Prob.FreeOmega.Measure`. It needs only native measure/omega operations, not
native separation or countable-AE laws, and remains closed under the global
context. Coincidence now consumes a probability-owned fact. No global instance
or compatibility alias is introduced.

## Remaining FreeOmega algebra: classified, not moved

| Declaration | Actual route | Stage 1 disposition |
| --- | --- | --- |
| `peutt_bind_ret_l` | observe equality → pstruct → peutt | retain |
| `peutt_bind_ret_r` | structural right unit → peutt | retain |
| `peutt_bind_assoc` | structural associativity → peutt | retain |
| `peutt_fmap_id` | behavioral right unit | retain |
| `peutt_fmap_compose` | structural bind algebra → peutt | retain |
| `peutt_fmap_bind` | behavioral associativity | retain |

Their compiled signatures fix FreeOmega and require native CoreLaws and omega
operations; the source section's AELift binder is unused in these six results.
All six statements/proofs are unchanged. Moving them now would conceal the
actual unresolved dependency: the FreeOmega-only structural-to-behavioral
bridge. Stage 2 must investigate that bridge first, without introducing a
`PStructPeuttLaws`-style conclusion-as-capability.

## Preservation and validation

`audit_generic_algebra.py` freezes all unrelated baseline `.v` files, verifies
the exact Dirac relocation and the exact retained FreeOmega equations, and
protects the old regression bodies. The generic profile must match `Eq.Bind`.
It checks all 465 old contracts, permits only the two explicitly generalized
Proper owners/types, and records their before/after values in
`GENERIC_ALGEBRA_CONTRACT_CHANGES.json`. The independent Stage 1 compiled
snapshot is `GENERIC_ALGEBRA_CONTRACTS.json`.

The previous bind-extraction audit is not weakened: its unit tests now run
against its frozen `ad8705f` source snapshot, just as earlier migration tests
run against their accepted snapshots. This new audit guards the live sources.

All old Gate M compiled contracts must remain exactly identical; three new
rewriting clients are added to the separate unsafe-hierarchy snapshot. The
logical axiom whitelist, qlift/approximation, canonical routing, core probability
classes, and MathComp native mathematics remain unchanged.

Local validation:

- Full `opam exec -- dune build`, including AllImports: passed. There are
  313 modules: 311 Gate S and the same two explicitly unchecked Gate M files.
- All 152 tool tests passed; the 25 Stage 1/soundness tests were rerun after
  adding the final SubEnumR probes and also passed.
- Architecture, aggregate coverage/order, public surface, source safety, and
  unchanged capability declarations: passed.
- 465 compiled mainline contracts: passed, with only the two reviewed Proper
  generalizations. The exact before/after ledger records both.
- Stage 1 preservation/compiled audit: passed for 302 frozen modules and all
  16 new contracts, including exact recovery of the two old FreeOmega types.
- Soundness audit: 199 frozen contracts, 36 generic validation endpoints,
  18 finite-real joint endpoints and 80 native MathComp endpoints passed with
  the unchanged logical whitelist.
- Dedicated Gate M audit: 33 direct endpoints plus six safe native controls
  passed; old entries are byte-for-byte identical, and three new clients retain
  explicit unsafe-hierarchy/session flags. This is not a universe-safety claim.

- Joint kernel check of nine safe module bodies: passed, including AllImports.
  This used `coqchk -norec`: compiled dependencies are trusted, not recursively
  rechecked. Gate M is excluded; this is not a whole-library kernel audit.

Reproduce the checks with:

```sh
opam exec -- dune build
python3 -m unittest discover -s tools -p 'test_*.py'
python3 tools/audit_architecture.py --check
python3 tools/audit_api.py --surface-only
python3 tools/audit_soundness.py --check
python3 tools/audit_generic_algebra.py --compiled --kernel
python3 tools/audit_mathcomp_direct.py --gate M
```

CI is intentionally outside this task. Stage 1 is ready for review; no Stage 2
bridge, Stage 3 iteration, or Stage 4 interpreter proof was changed.
