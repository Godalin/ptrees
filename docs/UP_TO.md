# Coinduction up to program contexts

The behavioral generator and `peutt` are unchanged. These are proof rules
for reducing the candidate relation, not additional equivalences or axioms.
Import `PTree.Eq` for the public rules, or their explicit owners below.

| Rule | What the closure may discharge | Owner |
| --- | --- | --- |
| `peutt_coinduction_upto` | an already established `peutt` pair | `Eq/PEutt` |
| `peutt_coinduction_upto_bind` | related prefixes, with candidate/known return continuations | `Eq/PEutt` |
| `peutt_coinduction_upto_prob` | a native relational lifting, with candidate/known sampled continuations | `Eq/UpToProb` |

`bind_upto_closure_bind` and `prob_upto_closure_sample` are introduction
rules: clients provide the mathematical certificates, not the existential
encoding of the closures. All three rules allow heterogeneous return
carriers and arbitrary return relations.

## Soundness and scope

The new sampling closure contains the candidate, established `peutt`, and
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
and `Reply` supply the visible progress. This API is a one-context closure;
it does not claim arbitrary nested-context or combined bind/Prob closure.

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

`MixedHeadProtocol` now keeps roots and reply states. After
`Challenge`, up-to-Prob consumes a native coupling built by relational bind:
the shared Stop/Continue outcome is coupled diagonally, and each Continue
block uses the non-functional three-to-two joint
`[(1/3,(L0,false)); (1/6,(L1,false)); (1/6,(L1,true)); (1/3,(L2,true))]`.
`Stop` closes by the known return law. `Continue` enters the reply candidate
with both the current-state bridge and the sampled-state bridge. After
`Reply`, `bridge_next` chooses the new bridge on acknowledgement true and
the old bridge on false. Thus the coupling support actually closes the
recursive obligation. The three-state implementation and two-state
specification retain the original `3/8` and `1/8` quantitative queries.

The core theorem is `mixed_head_bridge`. `uniform3_no_deterministic_fair`
rules out *any* deterministic pushforward from the uniform three atoms to
the fair Boolean marginal. Since `L1` relates to either Boolean, symmetry
and transitivity yield the canonical endpoint `masked_protocol_equivalent`
without another coinduction. This does not claim three behaviorally
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
observable profile once, and a **local** `≈ₚ` expands directly to that raw
`peutt`. Thus the public conclusions read
`von_neumann_service ≈ₚ direct_fair_service` and
`masked_impl m ≈ₚ canonical_spec`, without a canonical-relation wrapper or new instances.
The service's bind expressions use the standard `b <- sampler ;; ...`
notation. Local `tree`, `state`, `progress` and up-to abbreviations hide
repeated type parameters, not proof obligations: complete-hitting progress
and the root/reply invariants remain visible in the proofs. Concrete
probability analysis retains its explicit measure interfaces where needed.
The original notation-only follow-up preserved its 69 compiled contracts.
The subsequent three-to-two case changes its programs and state types, but
does not change any generic theorem or backend.

The six new public/client endpoints are recorded in the existing
`GENERIC_ALGEBRA_CONTRACTS.json` suite; its earlier entries are preserved.
There is no new stage-replay audit or global typeclass hint.

## Original up-to implementation validation

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

## Three-to-two MixedHead follow-up

All case-specific mathematics and programs stay in `Examples/MixedHeadProtocol.v`.
`mixed_samples` composes the shared outcome kernel with the hidden-state
distribution only on Continue. This finite native bind is the concise
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
