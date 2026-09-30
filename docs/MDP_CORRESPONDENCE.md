# Backend-parametric MDP correspondence

The central result is generic, not a SubEnumQ coupling proof. The source is a
labelled, nonterminating MDP with every action enabled and total transition
rows. Its state, action and observation carriers need not be finite.

Under the existing native/frontier reflection and MDP-fragment laws:

```text
source MDP bisimilarity
    ↕ faithful representation of source kernel rows
native MDP bisimilarity
    ↕ generic encoding/reflection
peutt of encoded states
    ↕ generic MDP-fragment coincidence
trans_bisim of encoded states
```

## Generic owners and exact obligations

`Semantics/MDPEmbedding` already defines `MDP MN`, the independent source
bisimulation, and the coinductive `Vis Choose; Prob; repeat` encoding.
`mdp_represent` additionally accepts a source `D : MDP MS` and native rows
`kernel : states D -> actions D -> MN (states D)` with a totality proof.
It preserves the states, labels and actions. There is no new class or second
source-MDP definition.

Faithfulness is only a distribution-level obligation on these rows:

```text
forall relation s t a,
  lift_MS relation (transition D s a) (transition D t a)
  ↔ lift_MN relation (kernel s a) (kernel t a).
```

`mdp_represent_bisim_iff` derives source/native bisimulation equivalence by
coinduction in both directions. No conversion of *arbitrary* source measures
is required. This matters when the source carrier permits mass greater than
one but the actual MDP rows are total.

`Semantics/MDPReflection` owns the two resulting encoding endpoints:

- `mdp_represent_peutt_iff`: source bisimilarity iff encoded `peutt`;
- `mdp_represent_trans_bisim_iff`: source bisimilarity iff encoded
  `trans_bisim`, additionally requiring encoded states in the MDP fragment.

These compose existing theorems; they introduce no new tree coinduction or
coupling construction. Source-side requirements are just its existing MDP
operations and CoreLaws; no source omega-completeness is needed. Target-side
requirements are exactly the established generic reflection/coincidence laws.
In particular, **source/native faithfulness does not replace native/frontier
reflection**: lifting of mapped successor frontiers must reflect to native
lifting. The latter is a separate probability theorem, spelled out in
[Generic MDP consumers](GENERIC_MDP.md).

For an already-native source, `mdp_trans_bisim_iff_of_fragment` exposes the
same result directly under fragment membership. The older
`mdp_trans_bisim_iff` derives that membership from totality and encoded-head
support of successor frontiers; its signature and assumptions are unchanged.

## Verified finite rational instance

`Semantics/Backend/MDPEmbeddingSubEnumQ.v` retains:

```coq
subenumQ_mdp_trans_bisim_iff :
  forall (D : MDP SubEnumQ) s t,
    mdp_bisim (D := D) s t <->
    trans_bisim eq (mdp_encode s) (mdp_encode t).
```

The abbreviated statement above uses the explicitly selected observable
`FreeOmega SubEnumQ` frontier in the source. The theorem applies to labelled
total MDPs with arbitrary state/action/observation carriers and finite rational
transition measures. The total-transition obligation is already part of `MDP`.
States need not be finite, and the encoding need not be injective.

Its proof now directly instantiates `mdp_trans_bisim_iff_of_fragment`, using
the existing native reflection and `subenumQ_encode_mdp_state`. The concrete
head/peutt iffs similarly delegate to their generic owners. All old concrete
statements and logical assumptions are preserved; the obsolete import of the
FreeOmega-specific coincidence wrapper is removed.

The same file also verifies a genuinely different source representation:
`D : MDP EnumQ`. `enumQ_mdp_kernel` wraps each total finite rational row in
SubEnumQ's existing mass-bound certificate. `enumQ_mdp_kernel_total` and
`enumQ_mdp_kernel_lift` prove totality and faithful lifting; the latter is
definitional equality. Weights, order, duplicate entries and zero entries are
unchanged. There is no normalization or proof-irrelevance requirement.

`enumQ_mdp_peutt_iff` and `enumQ_mdp_trans_bisim_iff` instantiate the generic
representation endpoints. The resulting PTree native backend is **SubEnumQ**,
with observable `FreeOmega SubEnumQ` frontier, not raw EnumQ.

No top-level export or canonical relation routing changes are needed. Import
the concrete instance directly:

```coq
From PTree.Semantics.Backend Require Import MDPEmbeddingSubEnumQ.
```

For generic clients, import `PTree.Semantics.MDPReflection`. Existing
MathComp/SubEnumR clients of the generic native-source theorem remain unchanged;
this refactor does not add another model instance or expand their trust boundary.

## Paper statement and scope

> For a native/frontier model satisfying the generic reflection and
> MDP-fragment laws, any faithful representation of a total labelled source
> transition kernel yields a PTree encoding that preserves and reflects MDP
> bisimilarity, both for transition bisimulation and for `peutt`. We verify
> this representation for total finite rational kernels using
> `(SubEnumQ, FreeOmega SubEnumQ)`.

This is not a reconstruction theorem for arbitrary fragment inhabitants,
does not identify every PTree with an encoded MDP, and does not equate the
two tree relations outside the fragment. Nor does it claim that arbitrary
MathComp/infinite-support kernels discharge the required laws. No manuscript
source is tracked here; this is the repository's paper-facing statement.

## Checked clients

- `distinct_states_encoded_trans_bisimilar`: different source states and
  different successor kernels still match by observation classes.
- `different_successor_probabilities_not_trans_bisimilar`: identical
  current labels but next-label probabilities `1/2` versus `3/4` are separated.
- `MDPEmbedding.unlabelled_counter_encodings_equivalent`: source states are
  `nat`, with random transitions and two actions. This deliberately constant-label
  example tests infinite state carriers, not observable separation of counters.

The full-abstraction iff itself is audited at its production owner; regressions
use it on concrete positive and negative pairs instead of redeclaring the iff.
`represented_positive_pair` and `represented_probability_separation` reuse
those same labelled kernels through the EnumQ-to-SubEnumQ adapter. They check
both preservation and reflection across the distinct source/native carriers,
including the `1/2` versus `3/4` distinction. No new regression file is needed.

## Logical dependencies

The concrete compiled theorem has no extra capability arguments beyond `D`, `s`, `t`.
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
The production endpoint and retained transition clients are checked against
their recorded dependency sets; retired wrappers add no separate contract.

The generic representation-bisimulation theorem is closed under its explicit
context. The represented `peutt` theorem inherits only `eq_rect_eq`; the
represented transition theorem inherits exactly the existing generic
coincidence's classical/dependent-equality/relational-choice dependencies.
The two rational row obligations are closed under their explicit context.
New concrete endpoints inherit the same logical axiom sets as their existing
SubEnumQ counterparts, not additional transport or existence axioms.

Twelve compiled records (eight production endpoints and four concrete clients)
are registered as `mdp_correspondence`; four additional generic endpoints
extend the existing `generic_mdp` suite. Exact
signatures and assumptions are recorded in `MDP_CORRESPONDENCE_CONTRACTS.json`.
Per-endpoint exceptions only record the existing dependencies above; the global
soundness whitelist and Gate M policy are unchanged. No new audit script or
historical source replay is introduced.

```sh
python3 tools/audit_contracts.py --group mdp_correspondence
```

## Kernel-representation refactor: local verification

Baseline: `f8bb183`. No new modules, classes, coupling constructions, public
aliases or checker relaxations were introduced. Four existing theory/client
files changed; the main generic fragment theorem and probability backends did
not change.

- Full `opam exec -- dune build -j 2`: passed, including AllImports and
  extraction. Existing extraction warnings remain; Gate M compilation is not
  a universe-safety claim.
- All 148 tool tests passed after the build. An earlier overlapping run hit
  a temporarily absent generated `controller.ml` during re-extraction;
  the complete suite was rerun after the artifacts were rebuilt.
- All 491 central contracts unchanged. Generic MDP: 56 safe contracts
  (52 unchanged, four new); concrete correspondence: 12 contracts (six
  unchanged, six new). The 11 existing Gate M MDP contracts are unchanged.
- Every prior snapshot entry is preserved exactly; only new endpoints and
  their inherited per-endpoint axiom exceptions were appended. Neither the
  global logical whitelist nor the Gate M allowlist changed.
- Architecture, API surface, soundness source and contract metadata audits:
  passed. Still 433 modules; removing the obsolete concrete-to-FreeOmega
  coincidence import reduces direct local Require edges from 5851 to 5850.
- Joint `coqchk -norec` passed for `MDPEmbedding`, `MDPReflection`,
  `Backend.MDPEmbeddingSubEnumQ` and `Regression.Semantics.MDPEncoding`.
  Dependencies are trusted; this is not a recursive whole-library kernel
  audit. Native computation checks fell back to VM conversion.

No remote CI was queried.

## Original theorem-addition validation

The following records that addition, before redundant regression wrappers were
retired. Current pruning and validation are recorded in
[the regression policy](REGRESSION_ORGANIZATION.md).

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
