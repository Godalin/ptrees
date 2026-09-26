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
root. Explicit after-request hitting/frontier lemmas remain available for
the `Request; Reply true` probability theorem. The after-request equivalence
is a corollary of the service theorem and ordinary bind congruence.

`MixedHeadProtocol` now keeps roots and reply states. After
`Challenge`, up-to-Prob consumes the existing non-diagonal eight-to-four
native coupling. `Stop` closes by the known return law; `Continue` enters
the reply candidate, matches `Reply`, and returns to a root with the updated
hidden state. Its AST and finite
coupling certificate are unchanged, as are its quantitative statements.

`Regression/Semantics/UpToProb` checks the known-equivalence branch with
arbitrary sampled/return carriers and no backend import. The mixed protocol
checks actual recursive branches. Existing divergence and missing-mass
regressions remain in place. Algebraic factory/controller proofs are not
converted to coinduction.

The six new public/client endpoints are recorded in the existing
`GENERIC_ALGEBRA_CONTRACTS.json` suite; its earlier entries are preserved.
There is no new stage-replay audit or global typeclass hint.

## Local validation

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
