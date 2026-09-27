# Reusing silent-round analysis in eventful programs

Implementation baseline: `ecedda8`.

The accepted interface below is unchanged. Its subsequent
[absorbing-exit extension](ABSORBING_ITERATION.md) permits mixed Ret/Vis
frontiers without changing the native per-round requirement.

The interface is `Interp/FreeOmega/IterationSummary.v`. It combines existing
generic behavioral iteration congruence with `primitive_iter_cofinal`; it
does not postulate a new cofinality or iteration capability.

## Local certificate, complete frontier, selected observation

For `transition : I -> MN (I + A)`, the client supplies either:

- `step i ≈ₚ Prob (transition i) Ret`, to `iteration_frontier_summary`; or
- a complete hitting witness `FOSample (transition i) (FORet ∘ FHRet)`, to
  `iteration_frontier_summary_hitting`.

The conclusion is complete stable hitting of `iter step i` into
`iteration_frontier transition i`. This is the formal limit of complete
rounds, in **MF = FreeOmega MN**, not a native distribution. There is no
`no_event`, finite-state, finite-fuel bound, or total-mass premise. The
ambient signature may offer events; the certificate constrains the actual
step behavior. A step may contain unbounded internal computation if its
complete behavior has the supplied native-kernel summary.

The proof replaces each step using `peutt_iter_direct_rel`, reuses the
primitive-loop cofinality theorem, and transports the reference return-only
frontier back with `peutt_hitting_ret_only`. Return support is essential:
behavioral equality does not in general identify visible continuation trees
by literal equality.

Separately, `iteration_frontier_observes` accepts a native limit of only
`iteration_observation_round transition value n i`. It proves an observation
of the complete frontier, without asking for a native limit of the entire
state/result joint distribution. A client with no native observation limit
can still use the complete frontier theorem. No claim is made that every
arbitrary MF-valued step can be summarized by a native kernel.

## Actual clients

- **Operational VN:** raw two-draw rounds and the compiled kernel now share
  the same round-limit analysis. The raw witness is chosen to be the compiled
  return frontier; the old duplicate raw-loop schedule/observation/support
  proof is removed. Finite raw-round certificates remain.
- **Interactive VN:** `von_neumann_third_in_equivalent_to_fair` transports the
  closed component theorem to any event signature. The service consumes it
  directly. Its pre-existing scheduled AST witness and quantitative trace
  endpoints are retained, not replaced by a bare behavior theorem.
- **Adaptive:** a two-draw local hitting certificate replaces the manual
  three-primitive-step schedule. The state-dependent convergence argument,
  success support and bit-only relational lifting are retained. In particular
  the new bridge does not demand a complete finite state/bit limit law.

MixedHead, FactoryController and RandomWalk are not changed. This is not a
new universal `meas_iter` interface or a promise to hide their analysis.

## Assumptions and ownership

The new summary is native-parametric but **FreeOmega-qualified**, not an
arbitrary-MF theorem. It uses native Core/AELift, CouplingAE and CountableAE
capabilities and a native Omega structure, via existing completion laws.
Finite Ret/sample certificates additionally use DiracAE and BindAEExact.
It is owned by Interp because its proof consumes the direct iteration
machine; Eq has no new dependency on Interp.

The behavioral summary inherits functional extensionality and `eq_rect_eq`
from existing iteration/hitting proofs, not choice. The observation bridge
introduces no logical axiom. No capability or semantic definition is added.

One recorded helper-level tradeoff is deliberate: Adaptive `loop_hits`
now also depends on functional extensionality, because it reuses the generic
iteration proof. Conversely, `loop_heads_observes` no longer depends on
`eq_rect_eq`. Its AST and final behavior endpoints retain their existing
axiom sets. The contract changes are explicit, not a blanket snapshot refresh.

## Checks

`Regression/Semantics/IterationSummary.v` exercises an inhabited signature,
unbounded nat state/result carriers, a bit-only observation limit, a zero-mass
kernel and endless retry. VN and Adaptive supply the nontrivial probability
analysis clients. Neither a zero summary nor endless retry asserts AST.

Local verification:

- Full `opam exec -- dune build -j 2`, including safe AllImports and extraction
  targets. The two pre-existing Gate M files remain outside the universe-safe
  claim; their code and allowlist are unchanged.
- All 141 tool tests; architecture, public-surface and soundness source audits.
- 465 original main contracts unchanged; all 69 previous generic-algebra
  contracts unchanged, plus 11 new endpoint contracts. All 41 factory contracts
  checked with exactly the two helper assumption changes described above.
- Joint `coqchk -norec` passed for Hitting, IterationSummary, Operational VN,
  Interactive VN, Adaptive and the new regression. This checks these six
  module bodies while trusting dependencies, not a recursive whole-library
  kernel audit. Gate M is not among the checked modules.
- No remote CI result is claimed or required for this change.
