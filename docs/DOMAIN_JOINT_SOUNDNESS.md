# DS5a.3: arbitrary-carrier qlift joint realization

Baseline: **countable nat transport accepted at `b91df98`**.
This increment completes the general relational soundness target for
**admissible FreeOmega SubEnum endpoints**. It is submitted for acceptance;
DS5b, auxiliary-branch cleanup and Gate D are not part of this change.

## Endpoint and exact meaning

```coq
free_omega_qlift_sound
  (R : realType) {A B} (T : A -> B -> Prop)
  (t : FreeOmega SubEnum A) (u : FreeOmega SubEnum B)
  (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  free_omega_qlift T t u ->
  oval_coupled T (free_omega_domain Ht) (free_omega_domain Hu).
```

Here `qlift` uses the canonical SubEnum native interfaces, not an arbitrary
semantic lifting. `oval_coupled T L M` means there exists an actual
`J : OmegaVal R (A * B)` such that:

- For every bounded test `f` on `A`, `J(f ∘ fst) = L(f)`.
- For every bounded test `g` on `B`, `J(g ∘ snd) = M(g)`.
- `J` is concentrated on pairs satisfying `T` (`oval_ae J ...`).

The companion `free_omega_qlift_joint_mass_support` also exposes
`mass J = mass L = mass M` and zero expectation of the indicator of the
complement of `T`. No margin or row is normalized. A half-mass input produces
a half-mass joint, not a probability-one joint. The independently established
DS1b correspondence gives this OmegaVal joint its standard subprobability
measure meaning; this proof need not re-import the measure adapter.

## Proof: compose the accepted bridges

```text
raw qlift T t u + admissible endpoints
       ↓ free_omega_qlift_countable_constraints
countably supported OmegaVal margins + oval_bidual T
       ↓ oval_countable_transport_reduction
nat-coded margins + bidual for the valid-code relation
       ↓ oval_bidual_coupled_nat (b91df98)
actual joint on nat × nat
       ↓ oval_joint_decode
actual joint on A × B
```

`Common/CountableCoupling.v` packages this independent mathematical argument.
`oval_bidual_coupled_on_enumerations` accepts covers which may repeat values
and contain `None`; `oval_bidual_coupled` only requires countable support of
the measures. The carriers need not themselves be countable, inhabited or
equipped with decidable equality. Relations remain arbitrary predicates.

The coded relation admits only valid pairs of codes. Decoding therefore
preserves both marginals: invalid codes cannot leak positive mass. All this
mathematics was already established by the preparation stage; this increment
only composes it with the accepted nat existence theorem.

`oval_countable_coupling_iff` adds the reverse implication from an existing
joint to bidual. This is **external dual/joint equivalence**, not completeness
of syntactic `free_omega_qlift`.

`SubEnum/FreeOmega/JointSoundness.v` then contains only three short endpoint
proofs. It neither unfolds nor inducts over qlift. In particular, `FOQLComp`
may use inadmissible intermediate terms on another carrier. Only the final
two endpoints need valid probability interpretations; the all-raw bounded-test
bridge already accounts for every constructor in such a derivation.

## Equality and boundaries

`free_omega_qlift_eq_sound_via_joint` specializes the general theorem and
uses `oval_eq_coupled_iff` to recover DS3's bounded observational equality.
It does not assert that the existential joint is literally the same record
as DS5a.1's explicit diagonal construction.

This stage does not establish:

- A denotation or probability interpretation for arbitrary invalid raw terms.
- A converse from external coupling to syntactic qlift.
- General MathComp-native FreeOmega realization.
- Infinite interaction/path measures, new stable-hitting operations, or a
  replacement for the maintained canonical equivalence.

## Regression and architecture

The regression calls the final existence theorem, not a supplied transport
plan. It covers duplicate/invalid codes, empty carriers and empty relations,
heterogeneous bool/nat partial-mass endpoints, the infinite-support geometric
fixture, and genuinely higher-universe carriers whose values are types.

Most importantly, the heterogeneous and equality tests reuse actual
`FOQLComp` derivations through the known-inadmissible `alternating_bool`.
Another test checks that raw reflexive qlift still does not imply validity.
Mass and off-relation support are checked on the resulting joint itself.

Both new theory modules are one-way external-validation modules. Only the
explicitly named Common adapters may join Domain with independent scalar
transport. Domain still depends only on Domain and mathematical libraries.
The mainline Eq/Interp/API/Examples dependency closure cannot reach either
adapter. Import-boundary tests also check that the new external layer does
not load FreeOmega, SemanticMeasure or PTree; the final bridge does not load
PTree or the MathComp measure adapter.

## Verification protocol

```sh
opam exec -- dune build
python3 tools/audit_domain_joint.py --check
python3 tools/audit_architecture.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
opam exec -- coqchk -silent -R _build/default/theories PTree \
  PTree.Prob.Backend.Common.CountableCoupling \
  PTree.Prob.Backend.SubEnum.FreeOmega.JointSoundness \
  PTree.Regression.Probability.FreeOmegaJointDomain
```

The source audit freezes all 249 earlier theory modules byte-for-byte, except
the three exact AllImports additions. The compiled audit records 18 endpoints
and checks the unchanged logical-assumption whitelist. No transport-existence
capability, new probability axiom or second free construction is introduced.
Historical incremental audits remain pinned to their accepted revisions;
their compiled contracts and the 306/25 mainline snapshots are checked again.
Targeted recursive kernel checking is not the whole-library Gate D audit.

### Local verification results

- Full `dune build`, including `AllImports`: passed.
- Joint recursive `coqchk` of both new theory modules and the new regression,
  with all their dependencies and without `-admit`: completed successfully.
- Byte-exact preservation of 249 earlier theory modules, apart from three
  specified aggregate imports: passed.
- All 18 compiled contracts and `Print Assumptions` checks: passed against
  the unchanged whitelist. The final bridge inherits the existing classical
  choice/extensionality and `eq_rect_eq` dependencies; it declares no new axiom.
- Architecture/import closure checks and all 91 audit-tool unit tests: passed.
- DS1a/DS1b/DS2/DS2.5/DS3/DS4/DS5a.1/DS5a.2a/DS5a.2b/DS5a.2c compiled
  snapshots: unchanged, with the previously declared relocation normalization.
- 306 public/helper and 25 capability endpoint snapshots: unchanged.
- `git diff --check`: passed. No remote CI result is claimed.

DS5a's general relational soundness goal is complete in the stated
SubEnum/admissible-endpoint scope, pending acceptance of this increment.
