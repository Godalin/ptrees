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
remains available. This work does not claim to discharge native reflection for
SubEnumR or direct MathComp; external OmegaVal realization alone is not an
internal native-reflection instance.

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
  client additionally exposes total-map as an obligation; this change does not
  claim that all MathComp MDP backend obligations are discharged.
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
