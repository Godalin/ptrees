# Finite-real completion: external joint realization

Baseline: `784d02a`. This closes backend-specific joint realization for
`FreeOmega (SubEnumR R)` and stops the coupling-soundness workstream. Generic
validation remains bounded-test/bidual soundness; no arbitrary-native joint
existence capability, new probability class, or heterogeneous-backend relation
is introduced. MathComp is a separate next stage, not part of this change.

## Countable support, before relational reasoning

`Prob/Backend/SubEnumR/FreeOmega/CountableSupport.v` defines
`subenumR_free_omega_enumerate : FreeOmega (SubEnumR R) A -> nat -> option A`.
Ret enumerates one value, Zero none, Sample pairs a finite native-list index
with a continuation code, and Lub pairs a chain index with a term code.

`subenumR_free_omega_enumerate_covers` proves structural AE concentration for
every raw term. This is only a cover, not an injective enumeration of exactly
the positive-mass values: duplicates and zero-weight entries are harmless.
No countability, inhabitedness or decidable equality is required of `A`.
The proof recurses on syntax, never on qlift.

`model_upper_ae_ext` and the existing native AE interpretation link then yield
`subenumR_free_omega_model_enumerated` and
`subenumR_free_omega_model_countable`: a modelable endpoint denotes an
`OmegaVal` concentrated on that cover. Invalid raw Lubs still have a cover;
this is not a validity certificate.

## Final bridge

`Prob/Backend/SubEnumR/FreeOmega/JointRealization.v` proves:

```coq
subenumR_qlift_sound :
  free_omega_qlift T t u ->
  oval_coupled T (free_omega_model Ht) (free_omega_model Hu)
```

Here `Ht` and `Hu` certify `free_omega_modelable` under the concrete native
interpretation `subenumR_domain`; `R : realType`, arbitrary result carriers
`A,B`, and `T : A -> B -> Prop` remain parameters. The entire proof is:

```coq
intro H.
exact (oval_bidual_coupled (subenumR_free_omega_model_countable Ht)
  (subenumR_free_omega_model_countable Hu) (subenumR_qlift_bidual Ht Hu H)).
```

There is no qlift induction or intermediate-validity requirement. The existing
all-raw bounded-test bridge handles quotient derivations; the existing Common
transport theorem constructs the actual joint. No transport proof is copied.

Two corollaries expose the result:

- `subenumR_qlift_joint_mass_support`: an actual `OmegaVal R (A * B)` witness,
  exact bounded-test marginals, its mass equal to both endpoint masses, and
  zero expectation of the complement-of-relation indicator. Subprobability
  mass is preserved without normalization.
- `subenumR_qlift_eq_sound_via_joint`: equality lifting yields `oval_eq`,
  agreeing with existing bounded-test equality validation. It does not assert
  that the chosen joint is literally the separately constructed diagonal.

## Checked examples and architecture

`Regression/Probability/SubEnumRJointRealization.v` uses the existing retry
prefixes driven by `sqrt(1/2)`-weighted native coins. Their increasing Lub and
its Boolean-complement output are modelable and qlift-related; the final
theorem produces a relational external joint for this unbounded computation.
This uses real coefficients directly, but does not claim an irrationality
proof for that coefficient or a new termination-probability calculation.

Other contracts cover equality agreement, an invalid-but-enumerable raw Lub,
an actual joint with mass exactly `1/2`, and independently quantified large
universe heterogeneous return carriers. Negative import checks exclude the
rational native backend and PTree reasoning from this regression's imports.
Only the three new modules and AllImports additions affect `.v` sources.
Old DS proofs, generic behavioral/validation theory, and public facades stay
unchanged. The new adapters are external validation, never mainline premises.

## Reproducible local checks

```sh
opam exec -- dune build
python3 tools/audit_architecture.py --check
python3 tools/audit_api.py --check --surface-only
python3 tools/audit_soundness.py --check --real-joint-only
python3 tools/audit_assumptions.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Prob.Backend.SubEnumR.FreeOmega.CountableSupport \
  -norec PTree.Prob.Backend.SubEnumR.FreeOmega.JointRealization \
  -norec PTree.Regression.Probability.SubEnumRJointRealization
```

The compiled realization audit checks 18 new endpoints against the existing
logical-axiom whitelist; the 505 frozen signature/assumption snapshots are not
regenerated. Source audits forbid qlift constructor analysis in the final
bridge and quotient dependencies in the countable-cover proof. The kernel
command checks the three new module bodies jointly, trusting compiled
dependencies; it is not the whole-library Gate D audit. CI and environment
changes remain out of scope.

## Verification result

- Full local build, including AllImports: passed (270 modules).
- Architecture inventory, API surface and soundness source contracts: passed.
- All 57 tool tests: passed.
- All 18 new compiled endpoint/assumption checks: passed under the unchanged
  logical-axiom whitelist.
- All 505 frozen compiled signatures and assumptions: unchanged.
- Joint targeted `coqchk -silent -norec` of the three new modules: passed.
- No new axiom, probability class, unfinished proof, unsafe universe setting,
  environment change, or CI check. MathComp work has not started in this stage.
