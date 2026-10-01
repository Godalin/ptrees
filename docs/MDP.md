# Labelled transitions and MDP correspondence

The CTree-inspired comparison semantics is distinct from canonical `peutt`.
`trans` sums the original mass of matching stable heads; it neither selects
one head nor conditions on an enabled event. `trans_bisim` additionally
compares current return and offered-event observations. Whole-continuation
correlation can distinguish `peutt` from this per-action comparison.

## Public theorem chain

```coq
From PTree Require Import Semantics.
```

| Owner | Endpoint / role |
| --- | --- |
| `Semantics/TreeTransition` | `trans`, `tree_return_observation`, `tree_offered_event_observation` |
| `Semantics/TreeTransitionBisim` | `trans_bisim`, unfold/fold/coinduction, reflexivity/symmetry/transitivity |
| `Semantics/TreeTransitionSoundness` | `peutt_trans_bisim` |
| `Semantics/MDPCoincidence` | `mdp_state_peutt_trans_iff` |
| `Semantics/MDPReflection` | Encoded source-MDP correspondence |

`trans_bisim_equivalence` is homogeneous (`RR := eq`), not an Equivalence
instance for every return relation. Its proof needs frontier Core laws beyond
the operations, not native laws, hitting existence or omega laws. Soundness
and fragment coincidence have stronger bind/order/omega/AE and Dirac/support
profiles. These are conditional generic theorems, not facts about all possible
measure representations. The old `tree_trans*` names have no compatibility aliases.

On two qualifying `mdp_state` trees, `peutt` and `trans_bisim` coincide.
This does not classify every PTree as an MDP or reconstruct a source MDP from
an arbitrary fragment inhabitant. The independent transition-side Tau proof
and the correlated-continuation counterexample test genuinely different
directions, not transition evidence manufactured only by peutt soundness.

## Faithful source kernels

[`Semantics/MDPEmbedding`](../theories/Semantics/MDPEmbedding.v) defines a
labelled nonterminating `MDP MN`: every action is enabled and each transition
row is total. State/action/observation carriers need not be finite. The
coinductive PTree encoding follows `Vis Choose; Prob; repeat`.

`mdp_represent` accepts a separately represented source `D : MDP MS` and
native rows `kernel : states D -> actions D -> MN (states D)`, preserving
states, labels and actions. Its row-level faithfulness obligation is:

```text
forall relation s t a,
  lift_MS relation (transition D s a) (transition D t a)
  <-> lift_MN relation (kernel s a) (kernel t a)
```

Only these total rows need representation; no conversion of every source
measure is required. `mdp_represent_bisim_iff` proves source/native equivalence.
`MDPReflection.mdp_represent_peutt_iff` and
`mdp_represent_trans_bisim_iff` compose that result with generic encoding and
fragment coincidence:

```text
source MDP bisimilarity
  <-> native MDP bisimilarity
  <-> peutt of encoded states
  <-> trans_bisim of encoded states
```

Source/native faithfulness does **not** replace native/frontier reflection.
Mapped successor lifting must reflect from the complete frontier to native
lifting; this is a separate probability theorem. Encoded fragment membership
also requires the established successor-totality and head-support properties.
`mdp_trans_bisim_iff_of_fragment` accepts membership directly; the convenience
`mdp_trans_bisim_iff` derives it from those properties.

## Concrete instances and their limits

- **SubEnumQ:** `Semantics/Backend/MDPEmbeddingSubEnumQ` specializes the generic
  proof. `subenumQ_mdp_trans_bisim_iff` applies to total finite rational rows,
  not only finite-state MDPs. `enumQ_mdp_kernel` wraps total EnumQ rows in the
  SubEnumQ invariant without changing weights, order, duplicates or zero entries.
  `enumQ_mdp_peutt_iff` / `enumQ_mdp_trans_bisim_iff` therefore encode into
  SubEnumQ PTrees, not an unbounded weighted execution carrier.
- **SubEnumR:** finite transport plus the raw quotient bounded-test bridge
  proves native reflection. `subenumR_validated_native_coupling` is an explicit
  validation-side proof value, **not an automatically installed instance**.
  Its OmegaVal dependency cannot be imported into model-independent mainline
  reasoning. Validation clients instantiate the same generic MDP theorems.
- **MathComp:** same-carrier `sem_lift_map_reflect` follows from Core/Bind and
  explicit right unit. Safe native map-mass/AE facts discharge totality and
  support. Gate M clients instantiate the whole generic chain with the existing
  gluing premise, without a further supplied reflection or relational-lub law.
  This is not a normally universe-checked recursive-frontier assembly.

No new MDP-level capability asserts the correspondence itself. No backend
copies the generic coinduction. Concrete correspondence inherits the logical
dependencies of all composed components: transition coincidence can add
classical/dependent-equality/choice dependencies beyond encoding alone.

## Interpretation within the fragment

Generic MDP preservation handles `handler : E ~> ptree F MN`:
selected source MDP heads must interpret to target MDP states. Then
`mdp_state_interp` preserves membership, target coincidence is on signature F,
and the guarded route transports source transition bisimulation to the target.

The atomic sufficient profile remains homogeneous `E -> E`: event relabelling,
inverse labels and total-map obligations are not a heterogeneous handler
interface. Backend total-map theorems discharge appropriate obligations without
normalizing partial mass. Neither the atomic result nor generic guarded
preservation says every arbitrary handler preserves `trans_bisim`.

See [backend assumptions](BACKENDS.md), [interpreter algebra](INTERPRETERS.md),
and [verification](AUDITING.md). Paper claims should state the reflection and
fragment conditions, followed by the verified finite-rational instance; do not
advertise a general measurable-MDP representation or reconstruction theorem.
