# Coinduction up to program contexts

The behavioral generator and `peutt` are unchanged. These are proof rules
for reducing the candidate relation, not additional equivalences or axioms.
Import `PTree.Eq` for the basic rules, and `From PTree.Eq Require Import
UpToBind.` for the bind/visible-context composition rule.

| Rule | What the closure may discharge | Owner |
| --- | --- | --- |
| `peutt_coinduction_upto` | an already established `peutt` pair | `Eq/PEutt` |
| `peutt_coinduction_upto_bind` | related prefixes, with candidate/known return continuations | `Eq/PEutt` |
| `peutt_coinduction_upto_bind_vis` | related prefixes, with a common visible context before candidate re-entry | `Eq/UpToBind` |
| `peutt_coinduction_upto_prob` | a native relational lifting, with candidate/known sampled continuations | `Eq/UpToProb` |

`bind_upto_closure_bind` and `prob_upto_closure_sample` are introduction
rules: clients provide the mathematical certificates, not the existential
encoding of the closures. `vis_upto_closure_vis` composes a visible context
from pointwise candidate obligations on its responses. All rules allow heterogeneous return
carriers and arbitrary return relations.

## Soundness and scope

The bind/visible rule is a small derived rule: apply existing up-to-bind to
the candidate extended by one common `Vis` context. Candidate roots use the
client's progress proof; visible contexts progress by `stable_hitting_match_vis`
and re-enter the original candidate. Thus clients need not enumerate reply
states themselves. This is one layer of visible context inside bind closure,
not an unrestricted recursively nested context closure. It retains the existing
bind-cofinality premise and frontier Core/Bind/Order/Omega/Cofinality/Diagonal/
Selection laws; no new capability, native law, or logical axiom is introduced.

The sampling closure contains the candidate, established `peutt`, and
one pair of `Prob` contexts. Its sampling constructor requires
`sem_lift XR mu nu` and, for every related sampled pair, either the candidate
or established `peutt` on the continuations. It does not select individual
atoms, normalize distributions, or require mass one.

The key theorem is `prob_upto_closure_compatible`. Given candidate progress
to the closure, it proves progress for the entire closure. It selects
complete continuation frontiers using `SemanticOmegaSelection`, applies
candidate progress (or unfolds known equivalence) at those witnesses, then
uses `mixed_lift_bind` to couple the complete sampled frontiers. Hitting
uniqueness handles arbitrary witnesses. The final coinduction theorem uses
the existing compatible-closure GFP rule. Neither proof calls
`peutt_prob` or assumes the desired contextual equivalence.

Its requirements are the existing native Core laws; frontier Core, Bind,
Order, Omega, Cofinality and Selection; and Mixed laws/omega laws. No
diagonal, commutativity, totality, external probability model, or new
capability is required. These remain explicit generic assumptions, not a
claim that every conceivable backend automatically satisfies them.
`Print Assumptions` reports the generic compatibility/coinduction theorems
and the bind introduction helper closed under the global context: no
additional logical axioms accompany these conditional generic statements.
The two concrete service/protocol equivalence endpoints inherit only the
existing dependent functional extensionality and `eq_rect_eq`; their new
proofs do not add a choice or excluded-middle dependency.

**Internal sampling is not a guard.** The premise is complete
stable-hitting progress, not a syntax-level step. Simply encountering
`Prob` never licenses a recursive call. In the protocol client, `Challenge`
and `Reply` supply the visible progress. The sampling closure admits one
native node; up-to-bind can instead consume a proved relation between
multi-node sampler programs, as in MixedHead below.

## Two clients, different uses

`InteractiveVonNeumannService` now keeps only the service root and
`publish b` pairs in its candidate. After `CoinRequest`, up-to-bind consumes
the proved sampler equivalence; after `CoinReply`, the proof returns to the
root. The sampler equivalence now reuses the closed VN component transported
to the service signature. The service's original complete AST witness is
retained; its totality follows by return-frontier transport. Only the direct
after-request frontier is needed for the `Request; Reply true` probability
theorem; the redundant VN-side construction has been removed. The
after-request equivalence is a corollary of the service theorem and ordinary
bind congruence. See [iteration summaries](ITERATION_SUMMARY.md).

`MixedHeadProtocol` keeps only loop entries in its local candidate. Its programs have
different internal shapes. The implementation draws a `3/4`-biased Boolean,
a fair branch selector, and a ternary payload implemented by a `1/3` coin
followed, only on failure, by a fair coin. Thus each round uses three or four
native Boolean `Prob` nodes. The specification uses **one** `Prob` over the
existing `mixed_samples uniform2 c` distribution; its native `sem_bind`
definition does not introduce extra PTree nodes.
The programs use the generic `sample` combinator and monadic sequencing for
these draws, and `trigger Challenge` for the initial interaction. The Reply
constructor stays explicit to guard recursion. These combinators add no Tau
steps; the proof removes their administrative return-binds by `observe_bind`.

Both Stop and Continue carry a payload, preserving the heterogeneous-return
extension. There are no named sampler subprograms or pre-proved sampler
equivalence wrappers. After `Challenge`, **up-to-bind/Vis** exposes two obligations:
relate the finite prefixes, then relate their continuations. The main proof
constructs explicit hitting witnesses in the prefix subgoal and consumes the
native distribution calculation and joint there; no recursive frontier is
selected. The shared Stop/Continue outcome is coupled
diagonally, and **both** blocks use the same non-functional three-to-two joint
`[(1/3,(L0,false)); (1/6,(L1,false)); (1/6,(L1,true)); (1/3,(L2,true))]`.
Its left/right marginal and support obligations are discharged directly
inside `coupling32_lift`, without separately named preparatory lemmas.
`Stop` returns `(b,h) : bool * hidden3` on the left and
`(b,j) : bool * bool` on the right. The return relation preserves `b` and
requires `bridge h j`; the known heterogeneous return law closes this branch.
`Continue` composes the Reply context directly in the main proof, using both
the current-state bridge and the freshly sampled bridge. After
`Reply`, an inline case split chooses the new bridge on acknowledgement true
and the old bridge on false. Thus the coupling support actually closes the
recursive obligation. The three-state implementation and two-state
specification retain the original `3/8` and `1/8` quantitative queries.

One-use bookkeeping stays at its use site: the five native mass bounds are
proved inside the coin/kernel constructors, and the final query probability
is computed at the end of its proof. The query uses its selector directly,
without a separate function-equality lemma or a local appeal to functional
extensionality. This does not remove extensionality inherited from library
theorems. The substantive finite distribution and joint analyses remain
separate from the compositional program proof.

The case also needs no hand-written `change` of backend goals: the native
lemmas apply by conversion. Only the no-deterministic-map counterexample
first simplifies its mass hypothesis with `cbn`, exposing the three Boolean
images for case analysis.

Native `sem_lift` statements and `free_omega_denotes` infer their backend
arguments from the distributions. Hitting/query calls retain only
the explicit omega and mixed structures needed for inference; their measure
instance follows from the omega structure. The backend profile remains fixed
at the top of the file, without new instances or search hints.

The main proof does not flatten probability lists or add intermediate
sampling states to its invariant: Ret closes by the heterogeneous return
law, and Continue handles Reply before re-entering the loop candidate. The finite-prefix bind in
the corecursive definitions passes ordinary guard checking.

The core theorem is `masked_protocol_equivalent`. `uniform3_no_deterministic_fair`
rules out *any* deterministic pushforward from the uniform three atoms to
the fair Boolean marginal. `masked_protocol_equivalent m` starts the
specification at `abstract_state m`, with no caller-supplied bridge premise;
the proof establishes the initial relation internally. This deterministic
initialization is not a pushforward of the uniform sampling law. No symmetry
or transitivity of the heterogeneous return relation is assumed.
`masked_public_protocol_equivalent` erases the payload with generic relational
bind and recovers ordinary Boolean `peutt eq`, without another coinduction.
This does not claim three behaviorally
distinguishable implementation states: the hidden states are unobservable;
the non-functional requirement is about the native marginals and the
displayed recursive proof, not uniqueness of a behavioral bisimulation.

`Regression/Semantics/UpToProb` checks the known-equivalence branch with
arbitrary sampled/return carriers and no backend import. The mixed protocol
checks actual recursive branches. Existing divergence and missing-mass
regressions remain in place. Algebraic factory/controller proofs are not
converted to coinduction.

### Reading notation

Both clients follow FactoryController's presentation: setup fixes the
observable profile once, and **local** `≈ₚ` / `≈ₚ[RR]` expand directly to that raw
`peutt`. Thus the public conclusions read
`von_neumann_service ≈ₚ direct_fair_service` and
`masked_impl m ≈ₚ[return_rel] mixed_spec (abstract_state m)`, without a
specification wrapper, canonical-relation wrapper or new instances.
The service's bind expressions use the standard `b <- sampler ;; ...`
notation. Local `tree`, `state`, `progress` and up-to abbreviations hide
repeated type parameters, not proof obligations: complete-hitting progress
and recursive state invariants remain visible in the proofs. Concrete
probability analysis retains its explicit measure interfaces where needed.
MixedHead's source has four layers: preparation (§1: protocol types, native
coins, observable backend profile), complete programs (§2), mathematical
preparation (§3: native distribution calculations and observation functions), and
final theorems (§4, including the local loop-entry invariant). On a first pass, read §2 and
`masked_protocol_equivalent` in §4. The proof itself unfolds the protocols,
constructs the finite prefix evidence, and composes Stop/Continue/Reply
obligations. It does not hide these steps in `impl_draw_related` or a
postfixedness wrapper, nor disguise heterogeneous coupling as equality
rewriting. Quantitative program-query facts are also established locally.
There are no global named frontier or query witnesses. The probability theorem
constructs the specification query and its denotation together in a local
existential, then transports that query through `masked_protocol_equivalent`.
Its one-shot specification is analyzed directly with the native-probability
hitting rule, without an intermediate return-only bind frontier. Two branch
placeholders let the Ret/Vis proofs infer the actual heads and recursive
continuation; the observation proof likewise infers the native Boolean
distribution. Neither witness repeats a program fragment. The final
probability introduction infers its witnesses from the supplied evidence.
The unused standalone implementation-frontier projection theorem has been
removed, along with its observation function and two local type abbreviations.
The three program endpoints are the heterogeneous bisimulation, its
public-Boolean corollary, and the selected-trace probability theorem.
Only native probability calculations and observation functions are prepared
before these theorems; their complete-hitting witnesses are not.
Documentation headings suffice; no parameterless Coq `Section` is needed.
The original notation-only follow-up preserved its 69 compiled contracts.
The subsequent three-to-two case changes its programs and state types, but
does not change any generic theorem or backend.

The client endpoints and the new generic visible-context rule are recorded in
the existing `GENERIC_ALGEBRA_CONTRACTS.json` suite. No new stage-replay audit,
capability or global typeclass hint is needed. Removing `canonical_spec` only
unfolds that wrapper in the two public behavioral statements; their logical
assumptions are unchanged. The case has no global `mixed_protocol_sim` and no
Reply-state enumeration. The pure state relation `bridge` remains essential:
the update removes administrative program contexts, not the recursive invariant.
The suite now records 134 endpoints: only the unused standalone hitting
endpoint was removed from the preceding 135-entry snapshot; every remaining
compiled signature and logical assumption set is unchanged. The two generic
visible-context introduction/coinduction rules are closed under the global
context. The 491 central contracts are unchanged; neither the axiom whitelist
nor Gate M is extended.

## Historical checkpoints

The following records describe earlier accepted versions, not the current
program shape or endpoint inventory. In particular, the named sampler
programs, specification wrapper and root/reply candidate mentioned below
have since been removed.

### In-place proof update

The in-place proof update removes the obsolete `mixed_head_bridge`,
`tri_sample_uniform`, and `impl_draw_related` contracts along with their
case-local wrappers. The main `masked_protocol_equivalent` statement has
not changed. The then-retained standalone hitting endpoint exhibited the
actual Challenge continuation and frontier instead of a named after-Challenge
subprogram; that unused endpoint has since been removed. Its logical axioms
were unchanged at this checkpoint. All other 132
entries match their previous compiled types and assumptions exactly; the
suite now has 133 entries. No axiom whitelist or central snapshot changes.
Local full build/AllImports, architecture/API/source checks, and the case's
`coqchk -norec` passed (dependencies trusted). No CI query.

### Original up-to implementation validation

- Full `opam exec -- dune build -j 2`, including AllImports, passed.
  The initial high-concurrency rebuild hit the existing 20-second limits in
  two unchanged factory proofs; the low-concurrency retry passed without
  changing their sources or timeout settings. Existing extraction warnings
  remain unchanged.
- 141 Python tests passed; all 31 architecture tests were also rerun after
  registering the precise `Eq -> Eq/UpToProb` export edge.
- Architecture, public-surface and source-soundness audits passed.
- All 465 mainline compiled contracts remain unchanged; the generic algebra
  suite passes all 69 endpoints (63 preserved, six added).
- Joint `coqchk -norec` passed for PEutt, UpToProb, its generic regression,
  MixedHeadProtocol and InteractiveVonNeumannService. MixedHeadProtocol was
  rechecked after the final root/reply simplification. Dependencies are
  trusted by `-norec`; this is not a whole-library recursive kernel audit.
- Gate M is unchanged and excluded from that targeted kernel check. No CI
  status is claimed.

### Three-to-two MixedHead follow-up

All case-specific mathematics and programs stay in `Examples/MixedHeadProtocol.v`.
`mixed_samples` composes the shared outcome kernel with the payload
distribution on both Stop and Continue. This finite native bind is the concise
implementation of the proposed sequential draws, not another interpreter
or a change to `peutt`/stable-head semantics.

The contract suite replaces the old Boolean-state
`masked_protocol_equivalent` signature with the three-state endpoint and
adds four contracts: `coupling32_lift`, `uniform3_no_deterministic_fair`,
`mixed_head_bridge`, and `masked_challenge_true_reply_probability`.
The other 130 safe generic-algebra entries are unchanged.

The finite coupling and non-functional-marginal certificates are closed
under the global context. The bridge and canonical program theorems retain
exactly the old functional-extensionality and `eq_rect_eq` dependencies.
The quantitative query additionally inherits classical choice and excluded
middle from finite-interaction query existence. Re-elaborating the old case
confirmed that it already had both dependencies; its newly recorded
per-endpoint exception does not expand the global axiom whitelist.

Local validation: full build including AllImports, architecture/API/source
audits, 142 Python tests, 465 unchanged mainline contracts, and the 135-entry
safe generic-algebra contract suite passed. Joint `coqchk -norec` passed for MixedHeadProtocol and UpToProb;
dependencies are trusted, not recursively rechecked. Gate M and CI are
outside this check.

### Heterogeneous return-payload follow-up

Baseline: `dd3b447`. This changes only the case and its documentation/contracts;
the generic up-to, bind, observation and probability infrastructure is reused.

| Endpoint | Current meaning |
|---|---|
| `mixed_head_bridge m z` | `bridge m z` implies `peutt return_rel (masked_impl m) (mixed_spec z)` |
| `masked_protocol_equivalent m` | The same heterogeneous relation against `canonical_spec m` |
| `masked_public_protocol_equivalent m` | Erasing both payloads recovers Boolean behavioral equivalence |
| `masked_challenge_true_reply_probability m c` | The selected Challenge/Reply prefix still has probability `3/8` or `1/8` |

The former program return types were both `bool`; now they are `bool * hidden3`
and `bool * bool`. `return_rel (b,h) (b',j)` means `b = b' /\ bridge h j`.
It neither equates the payloads nor erases their relation: the middle payload
relates to both abstract values, while `(L0,true)` and differing public bits
are rejected (`return_abstraction_boundary`). Both native blocks consume
`coupling32_lift`; there is no second transport construction.
For each shared outcome, its existing mass multiplies the same joint matrix;
the blocks are not conditioned or renormalized.

The former `mixed_spec_states_equivalent` helper used homogeneous equality
symmetry/transitivity through the implementation. That argument does not apply
to the new relation and is removed, not silently generalized. The canonical
specification is now indexed by the implementation's initialization. The main
bridge still allows every related pair, including both images of `L1`, and
`bridge_next` still supplies the response-dependent recursive invariant.

Quantitative transport uses `finite_interaction_query_related` on the actual
heterogeneous theorem. Only the resulting Boolean **measure** coupling is
reversed; the program relation is not treated as symmetric. Concrete rational
calculation stays in the finite-analysis helpers. There is no claim that the
return relation is equality, that the state map transports uniform measures,
or that this case has an extraction endpoint.

Contract migration is explicit: of the 130 safe generic-algebra entries at
this baseline, 127 are unchanged; the two behavioral statements now use
heterogeneous return carriers, and the quantitative statement now concerns
the implementation's paired return carrier. Three new entries record
`mixed_samples_lift`, `return_abstraction_boundary` and
`masked_public_protocol_equivalent` (133 in total). No Gate M contract changes.
The two behavioral endpoints retain exactly their former extensionality and
`eq_rect_eq` dependencies. The Boolean-erasure corollary has the same two
dependencies. The quantitative endpoint retains classical indefinite choice
but no longer depends on `Classical_Prop.classic`; no whitelist was expanded.

Local validation: full `dune build -j 2` including safe AllImports/extraction,
143 tool tests (plus a post-snapshot rerun of the 12 contract-tool tests),
architecture/API/source checks, the 133-entry generic-algebra suite and all
491 unchanged central contracts passed. The other 32 query groups were not
rerun for this case-only change.
`coqchk -norec` passed for the changed case's module body; its compiled
dependencies are trusted, not recursively rechecked. CI was not queried.

### Asymmetric MixedHead programs (historical)

Baseline: `65b210a`. Only this example, documentation and its contract
registration change; the generic theory, backend and Gate M are untouched.

The finite sampler executes `Prob` nodes in PTree, not just native list binds.
`tri_sample` returns `L0` immediately after a successful `1/3` draw and otherwise
uses a fair draw to return `L1` or `L2`. `impl_draw` first draws the `3/4` mask
and fair Stop/Continue selector, then samples the payload for **both** branches.
`spec_draw` directly samples the existing eight-outcome abstract distribution.
No new event or unbounded internal loop is introduced.

The proof has three visible layers:

1. Finite rational analysis verifies the compiled sampler distributions.
2. Explicit finite-hitting witnesses give `tri_sample_uniform` and
   `impl_draw_related`, preserving the same heterogeneous return relation
   and 3-to-2 joint. They do not select unknown recursive frontiers.
3. `mixed_head_bridge` uses the existing up-to-bind rule. Its candidate
   still contains only roots and replies; `bridge_next` handles the
   environment's keep/refresh response.

The complete frontier witness and both quantitative query values are retained.
All eight previously registered MixedHead endpoint types and assumptions are
unchanged, as are the other 125 safe generic-algebra entries. Three contracts
were added: `tri_sample_uniform`, `impl_draw_related`, and a standalone
implementation-frontier endpoint (136 safe entries in total, subsequently
pruned as described above). These inherit only
the existing functional extensionality and `eq_rect_eq`; no whitelist changes.

Local validation: full `opam exec -- dune build -j 2` (including AllImports
and extraction), 143 tool tests, architecture/API/source-soundness checks,
all 136 safe generic-algebra contracts and 491 unchanged central contracts
passed. Existing extraction warnings remain. The other 32 compiled query
groups were not rerun for this case-only change. `coqchk -norec` passed for
MixedHeadProtocol's module body, trusting its compiled dependencies rather
than recursively rechecking the library. No CI status is claimed.

### Case-local universe simplification

The five explicit `Polymorphic` declarations originally in MixedHead were unnecessary
for this concrete client: its response wrapper, response projection, event
family and two finite lifting certificates can use fixed inferred universes.
They are not a reusable universe-polymorphic effect API. That first change kept
the Boolean response wrapper and ordinary universe checking; the program/proof section's
existing `Set Universe Polymorphism` is unchanged. No generic library setting
or Gate M permission is modified. This deliberately removes case-local
universe generality, not a premise or a probabilistic law.

Validation of this follow-up: full build including AllImports, all 136
existing safe generic-algebra type/assumption contracts (no snapshot edits),
architecture/source-soundness checks, and the case's `coqchk -norec` passed.
The latter trusts compiled dependencies. No CI query or tool changes.

The subsequent program-first presentation preserves all 93 declarations
and all 136 contracts without refreshing a snapshot. The original three
sampler bodies and two protocol unfoldings were checked by `reflexivity`;
only bound-variable names and a reducible `let` change in the programs.
Full build/AllImports, architecture/API/source checks and the case's
`coqchk -norec` passed. Two unused handler imports were removed; the generic
theory and proof assumptions are unchanged. Tool tests were not rerun for
this source/documentation-only presentation change; CI was not queried.

With the concrete event family now monomorphic, a further simplification
removes `mixed_response`, `Response`, and `response_value`: both `Challenge`
and `Reply b` return ordinary `bool`. Program continuations and interaction
selectors use these Booleans directly. This changes the event response carrier
from a one-constructor wrapper to `bool`, not the finite probability kernels,
3-to-2 joint, or up-to-bind argument. It is not a claim of definitional equality
with the old event signature. Ordinary universe checking remains enabled;
no generic library setting or Gate M permission changes.

Validation of the direct-Boolean change: full build/AllImports, all 136
unchanged safe generic-algebra type/assumption contracts, architecture/API/
source-soundness checks and the case's `coqchk -norec` passed. The kernel check
trusts compiled dependencies. The contract query was rerun after the build
completed (an overlapping first attempt could not load the rebuilding module).
No contract snapshot edits, tool changes, or CI queries.

The four-layer presentation factors the duplicate recursive bodies into
`protocol draw old`, instantiated by `masked_impl` and `mixed_spec`. The
three finite sampler definitions are unchanged, and both existing one-step
protocol equations still prove by `reflexivity`. All 42 existing lemma,
theorem and example statements/proofs are unchanged modulo comments and
whitespace; their declaration order is reorganized. The initial parameterless
Section blocks were subsequently removed in a formatting-only follow-up.
Full build/AllImports, the 136
unchanged safe generic-algebra contracts, architecture/API/source checks,
and the case's `coqchk -norec` passed (compiled dependencies trusted).
No snapshot refresh, generic theory changes, tool changes, or CI queries.
