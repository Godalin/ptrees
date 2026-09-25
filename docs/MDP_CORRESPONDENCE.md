# Classical MDP correspondence: composed endpoint

`Semantics/Backend/MDPEmbeddingSubEnumQ.v` now provides:

```coq
subenumQ_mdp_tree_trans_bisim_iff :
  forall (D : MDP SubEnumQ) s t,
    mdp_bisim (D := D) s t <->
    tree_trans_bisim eq (mdp_encode s) (mdp_encode t).
```

The abbreviated statement above uses the explicitly selected observable
`FreeOmega SubEnumQ` frontier in the source. The theorem applies to labelled
total MDPs with arbitrary state/action/observation carriers and finite rational
transition measures. The total-transition obligation is already part of `MDP`.
States need not be finite, and the encoding need not be injective.

## Proof and scope

The proof is only composition:

1. `subenumQ_mdp_peutt_iff` identifies source bisimulation with encoded `peutt`.
2. `subenumQ_encode_mdp_state` supplies **both** fragment premises.
3. `free_mdp_state_peutt_tree_trans_iff` converts the encoded `peutt` iff to
   the raw-tree transition relation.

There is no new coinduction, coupling construction, class, inference hint or
semantic assumption. Generic and FreeOmega theory is unchanged. This endpoint
does not assert the converse encoding representation theorem, correspondence
for every backend, or equality of `peutt` and transition bisimulation outside
the MDP fragment. General strictness remains unchanged.

The owner stays the concrete comparison-semantics module. No top-level export
or canonical relation routing changes are needed. Import it directly:

```coq
From PTree.Semantics.Backend Require Import MDPEmbeddingSubEnumQ.
```

## Checked clients

- `LabelledMDP.labelled_transition_full_abstraction`: the complete iff on a
  labelled MDP.
- `distinct_states_encoded_tree_trans_bisimilar`: different source states and
  different successor kernels still match by observation classes.
- `different_successor_probabilities_not_tree_trans_bisimilar`: identical
  current labels but next-label probabilities `1/2` versus `3/4` are separated.
- `MDPEmbedding.counter_transition_full_abstraction`: source states are `nat`,
  with random transitions and two actions. This deliberately constant-label
  example tests infinite state carriers, not observable separation of counters.

## Logical dependencies

The compiled theorem has no extra capability arguments beyond `D`, `s`, `t`.
It is **not axiom-free**. Its `Print Assumptions` is the union of the existing
encoding/reflection and fragment-coincidence dependencies:

| Family | Actual constants |
| --- | --- |
| Extensionality | `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`, `FunctionalExtensionality.functional_extensionality_dep` |
| Dependent equality | `Eqdep.Eq_rect_eq.eq_rect_eq` |
| Classical logic / scalar model | `Classical_Prop.classic`, `ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec` |
| Choice / description | `Epsilon.epsilon_statement`, `boolp.constructive_indefinite_description`, `IndefiniteDescription.constructive_indefinite_description`, `Description.constructive_definite_description`, `RelationalChoice.relational_choice`, `ClassicalUniqueChoice.dependent_unique_choice` |

In particular, composing with coincidence inherits its relational/unique-choice
dependencies; saying merely "same assumptions as the encoding iff" would be
inaccurate. Comparing against the **union of components** adds no logical axiom.
The five new theorem/regression endpoints were checked against this union.

Eight compiled records (three existing components and five new endpoints) are
registered as `mdp_correspondence` in the current contract runner. Exact
signatures and assumptions are recorded in `MDP_CORRESPONDENCE_CONTRACTS.json`.
Per-endpoint exceptions only record the existing dependencies above; the global
soundness whitelist and Gate M policy are unchanged. No new audit script or
historical source replay is introduced.

```sh
python3 tools/audit_contracts.py --group mdp_correspondence
```

## Local validation

- Full `dune build`, including safe AllImports and the existing extraction
  targets, passed.
- All 465 existing central contracts remained exact; all eight correspondence
  contracts passed. Existing snapshot files were not refreshed.
- Current architecture, public-surface and source-safety checks passed.
- The 12 contract-runner tests passed; unrelated runtime tests and every other
  thematic contract group were not rerun for this small theorem addition.
- Joint `coqchk -norec` passed for the backend owner and both modified
  regressions. Dependencies are trusted; this is not a whole-library recursive
  kernel audit. Native computation checks fell back to VM conversion, as
  reported by `coqchk`.

No CI result is claimed by these local checks. Public facade/naming review,
the broader paper assumption table and case-study exposition remain separate
bounded follow-ups; this change only closes the composed MDP iff.
