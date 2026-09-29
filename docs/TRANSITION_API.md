# Transition comparison: API and safety boundary

This is the comparison semantics inspired by CTree-style labelled
transitions, not the canonical `peutt` relation. `trans` sums the original
mass of all matching stable heads; it does not select a head or condition
on an enabled event. `trans_bisim` also compares current return and
offered-event observations. Its definition and those observations are
unchanged by this API completion.

## Public entry and theorem chain

```coq
From PTree Require Import Semantics.
```

The curated entry now exposes these existing owners explicitly, without
selecting a concrete backend or importing interpreter theory:

| Public endpoint | Owner | Scope |
| --- | --- | --- |
| `trans`, `tree_return_observation`, `tree_offered_event_observation` | `Semantics/TreeTransition` | Raw-tree subkernels and current observations |
| `trans_bisim`, `trans_bisim_coinduction` | `Semantics/TreeTransitionBisim` | Independent greatest fixed point |
| `trans_bisim_refl`, `trans_bisim_sym`, `trans_bisim_trans`, `trans_bisim_equivalence` | `Semantics/TreeTransitionBisim` | Homogeneous return equality, `RR := eq` |
| `peutt_trans_bisim` | `Semantics/TreeTransitionSoundness` | `peutt RR t u -> trans_bisim RR t u`, for a common return carrier |
| `mdp_state_peutt_trans_iff` | `Semantics/MDPCoincidence` | Both trees must satisfy `mdp_state` |
| `mdp_trans_bisim_iff` | `Semantics/MDPReflection` | Native MDP bisimulation iff transition bisimulation of its encoding |

No compatibility aliases for the retired `tree_trans*` names are added.
The standalone `TreeTransitionBisim` module still does not load `PEutt`;
the public entry intentionally loads the comparison chain as well.

The three arrows are **conditional generic theorems**, not assertions that
every measure representation automatically satisfies their premises.
Soundness consumes the existing bind/order/omega/AE laws. Fragment
coincidence additionally needs its established Dirac/support laws.
The encoded MDP iff keeps mapped native/frontier lifting reflection,
successor totality and encoded-head support explicit. See
[generic MDP premises](GENERIC_MDP.md); the concrete SubEnumQ endpoint
remains `subenumQ_mdp_trans_bisim_iff` in
`Semantics/Backend/MDPEmbeddingSubEnumQ`.

## Equivalence proof and limits

The new symmetry and transitivity proofs use only the operations needed
to state `trans_bisim` and `SemanticMeasureCoreLaws`. They do **not** need
native laws, `BindLaws`, `OmegaLaws`, witness uniqueness, hitting existence,
or an assumption reflecting equality coupling to `sem_eq`.

- Symmetry uses the reversed candidate and reverses each measure match.
- Transitivity uses relational composition of the candidate. Bidirectional
  witness matching supplies a matching *same intermediate measure* for each
  composed lift. A middle successor head `h` supplies the middle tree
  `stable_head_tree h` in the recursive candidate.
- The proofs address return observations, offered events and transitions
  separately; they never replace the generator with action-only matching.

All three new public constants have `Print Assumptions = Closed under the
global context`, conditional on their explicit capability arguments. No new
class or semantic law is introduced. The global `Equivalence` instance is
for `trans_bisim eq` only, not for an arbitrary return relation.

Regressions exercise `symmetry`, `transitivity`, typeclass resolution and
`setoid_rewrite` with just this minimal generic context. The correlated
continuation counterexample also uses symmetry and composition on its
independently proved transition evidence, outside `peutt`. Distinct returns,
empty-response events and strictness regressions remain intact.

## MixedHead checkpoint

`830c772` already completed the 3-to-2 reconstruction. It uses a joint with
rows `(1/3,0)`, `(1/6,1/6)`, `(0,1/3)`, proves that no deterministic
pushforward has the same uniform marginals, and consumes its support in
`bridge_next` after `Reply`. The canonical endpoint and `3/8`, `1/8` queries
are preserved. No further MixedHead change is needed here; see
[the up-to proof](UP_TO.md).

## Gate S audit

The existing architecture checker reconstructs the actual compiled
dependency graph and rejects **every** edge from Gate S to Gate M. This
implies transitive isolation, not just absence of a direct import. Its
current root-closure check gives the following sizes (including the root):

| Root module | Closure size | Gate M modules |
| --- | ---: | ---: |
| `Eq/PEutt` | 13 | 0 |
| `Eq/PTreeKernel` | 11 | 0 |
| `Prob/FreeOmega/Validation/Quotient` | 19 | 0 |
| `Prob/Backend/SubEnumQ/FreeOmega/DomainSoundness` | 43 | 0 |
| `Prob/Backend/SubEnumQ/FreeOmega/JointSoundness` | 63 | 0 |
| `Prob/Backend/SubEnumR/FreeOmega/JointRealization` | 43 | 0 |
| `Eq/Backend/StableHittingDomainSubEnumQ` | 55 | 0 |
| `Examples/AdaptiveFactoryController` | 131 | 0 |
| `Examples/MixedHeadProtocol` | 75 | 0 |
| `Execution/Validation/SubEnumQ` | 60 | 0 |
| `Execution/Validation/UniformReplay` | 14 | 0 |
| `Semantics` | 22 | 0 |

Only `Eq/Backend/MathComp` and `Regression/Backend/MathComp`
remain in Gate M, outside safe AllImports. Source and build-flag checks
reject other checker bypasses. Gate S is **not** a claim of axiom-freedom:
existing classical/extensional assumptions and model premises remain
recorded in compiled contracts. No Gate M permission is added or widened.

Validation uses the existing architecture, API, source-soundness and compiled
contract tools; there is no new stage-specific audit framework. The three
new public equivalence constants are recorded in the existing
`generic_mdp` contract suite; old theorem signatures and assumptions are
preserved.

## Local validation

- Full `opam exec -- dune build -j 2`, including AllImports, passed. Existing
  extraction warnings remain; this is not a claim that the two Gate M
  modules are universe-checked.
- Architecture, public API and source-soundness audits passed; all 142 tool
  tests passed.
- All 465 mainline and eight concrete MDP correspondence contracts are
  unchanged. The generic-MDP suite passes 52 safe entries: 49 preserved and
  the three new equivalence entries. No axiom whitelist was expanded.
- Joint `coqchk -norec` passed for `TreeTransitionBisim`, `Semantics`,
  `MDPReflection`, the bisimulation/strictness regressions and
  `ArchitectureBoundaries`. This checks those six module bodies while
  trusting their dependencies, not a whole-library recursive kernel audit.
- No remote CI result is claimed. No foundation, backend, canonical routing,
  example program or runner semantics was changed.
