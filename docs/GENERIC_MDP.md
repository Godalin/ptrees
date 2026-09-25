# Generic MDP consumers

The MDP comparison and interpretation proofs now have generic owners. This
does **not** mean that every backend automatically satisfies every premise.

| Owner | Result | Additional probability obligation |
| --- | --- | --- |
| `Semantics/MDPReflection` | Native MDP bisimulation iff encoded head bisimulation / `peutt` | Mapped frontier lifting reflects to native lifting |
| `Semantics/MDPReflection` | Literal encoded transition iff, for any output witness | Output extensionality of `sem_lub` |
| `Semantics/MDPReflection` | Native MDP bisimulation iff encoded `tree_trans_bisim` | Also totality and encoded-head support of successor frontiers, plus fragment laws |
| `Interp/MDP` | MDP-state preservation, target coincidence, guarded transition preservation | Existing generic hitting/interp laws; selected-head handler contract |
| `Interp/Atomic` | Atomic transition-bisimulation preservation | Bind right unit; output extensionality of `sem_lub` |
| `Interp/MDPAtomic` | Atomic MDP invariant and state preservation | Output extensionality; totality under the atomic head map |

All five proofs are independent of FreeOmega and MathComp representations.
No new class, global inference hint, `qlift` rule or universe bypass is added.
Ordinary generic declarations retain only the Section hypotheses actually used
by their proofs; the compiled contracts record those signatures.

## Reflection is a probability theorem

The local reflection premise is precisely:

```text
lift rel (mixed_bind mu (ret ∘ f)) (mixed_bind nu (ret ∘ g))
  -> lift (fun x y => rel (f x) (g y)) mu nu
```

It does not mention PTree, MDP, coinduction or encoding. Decoders need not be
injective. `FreeOmegaNativeCouplingLaws` already supplies this fact via an actual
native joint witness; `free_omega_sampled_heads_reflect` is its probability-level
consumer. `Semantics/FreeOmega/MDPReflection` consequently works for arbitrary
native models supplying that existing optional law, not just SubEnumQ.

The established SubEnumQ endpoints keep their statements, but their reflection
coinductions now call the generic proof. Its unconditional concrete full iff
remains available. SubEnumR now has the explicit validation-side native
reflection construction described below, not an automatically registered
mainline instance. Direct MathComp native reflection remains open; external
OmegaVal realization alone is not an internal native-reflection instance.

## Atomicity: two previously implicit laws

The generic atomic proof needs these explicit *local* probability premises:

```text
sem_eq (sem_bind mu sem_ret) mu
sem_eq mu nu -> sem_lub c mu -> sem_lub c nu
```

They are not bundled into another typeclass and neither is a tree preservation
theorem. FreeOmega proves the first by structural bind-return lifting and the
second by transitivity of observable equality. MathComp already proves both in
its universe-checked `Kernel` module. Direct clients use those same native
proofs; no probability mathematics is moved into unchecked code.

Two other facts are derived from existing interfaces in `Prob/Interface/Omega`:

- `sem_bind_eq_l`: source equality congruence from constant limits, chain
  properness and bind continuity;
- `sem_eq_of_le_equiv`: mutual approximation implies equality, using constant
  chains and directed cofinality.

Neither derivation assumes the invalid converse `sem_eq -> sem_le`.

The existing FreeOmega atomic certificate and names are preserved. A transparent
fieldwise conversion specializes the generic certificate; the substantive
hitting and transition proofs are wrappers around the generic implementation.
The old graph-lifting helper retains its weaker native signature by using the
primitive quotient bind rule; it need not assume the whole native AELift
capability merely to apply that rule. The generic proofs
`atomic_finish_bind_of_ret_l` and `mdp_state_interp_of_ret_l` consume just the
left-unit equation. Their ordinary wrappers obtain it from BindLaws, whereas
the old FreeOmega wrappers discharge it by computation and reflexivity. This
avoids importing both an unnecessary AELift premise and the functional
extensionality used by other fields of the FreeOmega bind-law record.
The response-preserving event-permutation profile stays `E -> E`. Generic MDP
and guarded interpretation still support genuinely heterogeneous `E -> F`.

## Model boundaries

- SubEnumQ keeps the complete classical correspondence and the old atomic MDP
  specialization, including its proved total-map fact.
- FreeOmega specializations remain parameterized by native capabilities; there
  is no copied SubEnumR proof or new backend hierarchy.
- Direct MathComp instantiates generic MDP, guarded and atomic transition
  preservation. Its existing gluing premise remains explicit. The atomic MDP
  client now discharges total-map using the checked native mass theorem below;
  this does not discharge gluing or relational-lub closure.
- The two-file Gate M allowlist is unchanged. The new direct clients live in
  the already allowlisted regression, outside safe `AllImports` and safe kernel
  validation. Compilation of these clients is not a universe-safety claim.

The previous concrete correspondence report is retained as the record of that
endpoint. This report supersedes its statement that generic theory was unchanged.

## Assumptions and validation

- The two primitive left-unit consumers, generic `mdp_state_interp`, generic
  graph lifting, and the two new Omega helpers are closed under the global
  context, conditional on their explicit mathematical inputs.
- MDP reflection inherits `eq_rect_eq`. The full transition correspondence,
  guarded route and atomic transition theorem inherit classical/relational
  choice from existing transition existence/coincidence. They are not claimed
  axiom-free. FreeOmega specializations retain their established dependencies.
- The 465 central contracts, 8 concrete MDP correspondence contracts and 43
  direct MathComp contracts remain **exactly unchanged**, including their
  existing snapshot files. The two potential functional-extensionality
  increases discovered during development were eliminated, not accepted into
  refreshed snapshots.
- 25 new safe contracts and 4 direct clients are registered in the existing
  current-tree contract runner. No new auditor or historical replay is added.
  The direct query adapter now honors the runner's existing **per-endpoint**
  axiom exceptions, to record the inherited relational/unique-choice facts.
  Neither the global logical whitelist nor the unsafe-hierarchy reporting is
  weakened; tests reject exceptions for the wrong endpoint and unknown axioms.
- Full `dune build -j 4` passed, including safe AllImports, old regressions and
  extraction targets. The repository has 422 theory modules: 420 Gate S and
  the same 2 Gate M modules.
- Architecture, source-safety and public API audits passed; 266 public compiled
  contracts remained exact. All 124 tool tests passed; after the direct-audit
  adapter change, its affected 20 tests were rerun and passed.
- Joint `coqchk -norec` passed for all 11 changed/new safe theory owners.
  Dependencies are trusted; this is a targeted kernel check, not a recursive
  whole-library audit, and excludes both Gate M modules.

No remote CI result is claimed. Gate M compilation/assumption audits remain
explicitly distinct from normally universe-checked proofs.

## Follow-up: MathComp pure-map mass preservation

`Prob/Backend/MathComp/Kernel` proves `mathcomp_kernel_map_mass` for arbitrary
carriers, arbitrary functions (not necessarily injective), and arbitrary native
subprobability kernels:

```text
returned_mass (bind mu (ret ∘ f)) = returned_mass mu
```

The proof integrates the indicator of returned values. At the cemetery point
both sides contribute zero; at every returned value the pure continuation
contributes one. It requires neither gluing, totality, finite/countable support,
nor a PTree-level assumption. `mathcomp_kernel_map_total` derives totality as an
iff, so a pure map cannot normalize a partial distribution either.

The existing Gate M `direct_atomic_mdp` now supplies this safe native fact to
the unchanged generic theorem `MDPAtomic.mdp_state_interp_atomic`. Its explicit
`Htotal` premise is removed. The gluing premise and the two-file unchecked
assembly boundary are unchanged; all new probability mathematics is Gate S.

Safe regressions cover a partial Bernoulli followed by a constant map (mass
remains exactly `q`), a noninjective total map, and an empty source at zero mass.
The existing generic-MDP contract snapshot records the two native theorems and
these checks. Of its previous entries, only `direct_atomic_mdp` may change type;
its logical assumptions must remain unchanged. No new audit runner is added.

Follow-up local validation:

- Full `dune build -j 4` passed, including AllImports and the direct client.
- 465 central contracts and the 43 existing MathComp direct/control contracts
  remained exact. The generic-MDP suite passed with 30 safe and 4 direct
  contracts; only the intended direct atomic MDP type changed among old entries.
- `Print Assumptions` for the new native facts contains the existing MathComp
  propositional/functional extensionality and indefinite-description axioms.
  The direct atomic MDP endpoint's logical assumptions and unsafe flags are
  unchanged; the logical whitelist and Gate M allowlist were not modified.
- Architecture/source-safety audits and all 124 tool tests passed.
- Joint `coqchk -norec` passed for `Kernel` and `MathCompOrder`. This checks
  their safe module bodies while trusting compiled dependencies, not the whole
  library recursively; the unchecked direct client is excluded.

MathComp gluing/relational-limit existence remain separate future work.
CI was not consulted for this follow-up.

## Follow-up: SubEnumR native reflection, with explicit validation ownership

`SubEnumR/FiniteTransport` is ordinary native mathematics. The theorem
`subenumR_transport_of_mapped_tests` takes bounded-test inequalities on decoded
values and equality of actual mass, and constructs a finite joint on the
**original sample carriers**. It does not mention FreeOmega or OmegaVal.

The construction indexes the original finite lists (including duplicates and
zero entries). For a set of left positions, its decoded image supplies the
left indicator test, and its relational image supplies the right test. The
left position mass is bounded by the decoded-image mass even with duplicate
decoders. The resulting Hall inequality and equal mass feed the existing
`finite_real_transport`. The resulting matrix is enumerated as a native
SubEnumR joint, with exact marginals for arbitrary, even signed, tests.
`subenumR_lift_realization` packages this as `semantic_coupling`.

`SubEnumR/FreeOmega/NativeReflection` then consumes the existing all-raw
`subenumR_qlift_bidual_raw`, derives these test and mass premises, and obtains
`subenumR_native_quotient_coupling`. No qlift induction, admissibility premise
on derivation intermediates, external joint witness, or new class is used.
`subenumR_validated_native_coupling` supplies the existing optional
`FreeOmegaNativeCouplingLaws` as an explicit proof value, **not an Instance**.

This ownership distinction is deliberate. The reused scalar validation proof
depends on OmegaVal. Importing it into ordinary Eq/Semantics/backend modules
would violate the maintained one-way model-validation boundary. The new module
is explicitly classified as external validation; architecture tests reject
direct and indirect imports from mainline consumers. The native finite
transport module itself remains independent of validation. We do not weaken
the dependency policy or duplicate the entire raw quotient induction merely
to obtain an automatic backend instance.

Validation regressions consume the same generic correspondence proofs with
this explicit certificate: `mdp_bisim <-> peutt`, `mdp_bisim <-> head_bisim`,
and (using proved fragment membership) `mdp_bisim <-> tree_trans_bisim`.
There is no copied MDP coinduction. A negative inference check confirms that
importing the validation theorem does not install an automatic instance.
Further checks retain duplicate/zero-weight partial native marginals under
constant decoders, handle an empty carrier and empty relation at zero mass,
and decode unit samples to types in independently quantified universes.

Thus the mathematical native reflection obligation is proved for SubEnumR;
making it part of the **model-independent mainline import profile** is a
separate architectural decision, not claimed here. MathComp gluing and
relational-limit closure are unchanged.

SubEnumR follow-up local validation:

- Full `dune build -j 4` passed, including safe AllImports and existing clients.
- 465 central contracts remained exact; all previously recorded generic-MDP
  safe/direct contracts are unchanged. Fourteen new safe endpoints are added
  to the existing generic-MDP contract group, not a new audit framework.
- The native transport/reflection proofs inherit only existing whitelisted
  classical/extensional mathematical axioms. The transition-correspondence
  client also inherits `relational_choice` and `dependent_unique_choice` from
  generic coincidence; its exact endpoint receives the same two exceptions as
  `MDPReflection.mdp_tree_trans_bisim_iff`. The global whitelist is unchanged.
- Architecture/source-safety audits and all 125 tool tests passed. The source
  inventory is 425 modules, with the unchanged two-file Gate M boundary.
- Joint `coqchk -norec` passed for all three new safe modules. Dependencies
  are trusted, so this is not a recursive whole-library kernel audit.
- No existing production proof/definition or canonical route was modified;
  the only old theory source changed is the aggregate import list. CI was not
  consulted.
