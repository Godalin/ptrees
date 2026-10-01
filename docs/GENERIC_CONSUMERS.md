# Upper-layer consumer convergence

## Current capability and model status

Former FreeOmega-only structural/iteration boundaries have been generalized.
Historical stage reports and before/after snapshots remain in Git. See [generic structural consumers](GENERIC_RELATIONAL_CONSUMERS.md),
[eventful iteration](EVENTFUL_ITERATION.md), [direct iteration](DIRECT_ITERATION.md),
and [generic MDP consumers](GENERIC_MDP.md) for their current owners.

Three separate questions must be kept distinct:

1. Is there one backend-independent upper-layer proof?
2. Which probability certificates does that proof consume?
3. Has a particular model proved those certificates, and under which trust
   boundary and logical assumptions?

The following is a selected endpoint audit, not a theorem-by-theorem minimality
or logical-independence result. `G` means the existing explicit
`MathCompCouplingGluing R`; `L` means the still-supplied unrestricted
`relational_lub` certificate. All MathComp PTree clients remain in the
same two-file Gate M boundary. Native probability mathematics remains checked.

| Generic owner / endpoints | Probability requirements beyond chosen operations | FreeOmega over SubEnumQ / SubEnumR | MathComp |
| --- | --- | --- | --- |
| `Eq.Algebra.peutt_observe_eq`, `peutt_bind_ret_l` | Frontier CoreLaws only; omega **operations**, not OmegaLaws | Existing observable CoreLaws | Available with G; no L |
| `Eq.Bind.peutt_bind`, generic bind/fmap Proper | Core/Bind, Order/Omega/Cofinality/Diagonal, bind and mixed-bind order, directed cofinality, omega selection | Discharged by the generic completion profile | Available with G; no L |
| `Eq.Relation.peutt_of_pstruct/peutt_of_pstrong`, current right-unit/associativity proofs | Native/frontier Core, relational bind/mixed bind/zero, Order/Omega, relational-lub | Completion certificates discharge these | Current bridge/algebra route requires G + L |
| Eventful iter, full `iteration_uniform`, unrestricted interp | Existing scheduling/continuity profile, plus relational zero/lub; see compiled endpoint for mixed-bind requirements | Completion profile discharges these | Requires G + L |
| `Interp.Guarded.peutt_interp_guarded` | Bind/scheduling profile, CouplingAE, and the handler's semantic guard | Available for handlers satisfying the guard | Available with G and guard; no L |
| `Semantics.MDPReflection` full encoded correspondence | Mapped native/frontier reflection, successor totality/support and fragment laws | Q: native reflection instance; R: explicit validation-side certificate | Derived same-carrier reflection, native map mass/AE; G, no L |

The MDP row must not be read as an automatic SubEnumR mainline instance.
`subenumR_validated_native_coupling` is an explicit validation-side proof value.
Likewise, the MathComp MDP result does not discharge gluing or relational-lub.
The selected model instances also retain their recorded classical/extensional
logical dependencies; `generic` does not mean constructive or assumption-free.

### Premise cleanup: shallow left unit

At baseline `bf12340`, the compiled `Eq.Algebra.peutt_bind_ret_l` required native
Measure/Core, frontier Order/Omega and all four relational certificates, because
it invoked the full `pstruct -> peutt` bridge. This is unnecessary for this
particular equation: `observe (bind (Ret a) k)` reduces to `observe (k a)`.

The theorem now retains its name and equation but requires only frontier
Measure/Core, mixed operations and omega operations. `peutt_observe_eq` records
the reusable reason: equal observations may use `peutt` reflexivity directly.
Both proofs are closed under the global context. A generic regression declares
exactly this small profile; the MathComp client has no L parameter.
The established FreeOmega wrapper keeps its original statement.

Explicit applications passing the former four proof arguments must now simply
apply `Algebra.peutt_bind_ret_l`. The in-repository consumers have been updated.
Only the current compiled snapshot of this generic theorem is intentionally
weakened; historical before-snapshots are not rewritten.

Right unit, associativity, fmap composition, and structural/behavioral iteration
retain their current proof profiles. This review does **not** establish that
their relational-lub premises are necessary, nor that they cannot be weakened
by another proof. No theorem-level class is introduced to hide those premises.

### Ownership and deliberate limits

- Probability facts remain probability-owned: e.g. `sem_lift_map_reflect` and
  the explicit derived `coupling_ae_implies_ae_lift`. They are not new global
  inference routes or assumptions asserting a PTree conclusion.
- FreeOmega's main upper endpoints specialize generic proofs, but entire
  modules are not necessarily thin wrappers: structural lifting, observation
  transport and the older eventless iteration proof remain representation
  specific. No cleanup is justified solely by their directory names.
- Generic finite-interaction witness agreement is `sem_lift eq`, not an
  unprovided reflection to `sem_eq`. `Prₛ[t | pattern] = p` is a **rational
  certificate** requiring a finitely representable query, not a total real
  probability function on arbitrary programs.
- OmegaVal/standard-measure correspondence and countable external transport
  are independent mathematical-model results, not FreeOmega-only theory.
  Validation remains a one-way consumer, never a mainline dependency.
- `Execution.Runner` is generic in MN and its supplied sampler. Rational
  tickets and the uniform-entropy distribution theorem are SubEnumQ-specific.

No new probability class, global hint, canonical route, FreeOmega quotient
rule, or unchecked module is introduced by this follow-up. Numeric observation
extensions and a proof of unrestricted MathComp relational-lub are separate
future tasks, not hidden obligations completed by this cleanup.

## Current verification

The capability table is a selected profile review, not a minimality claim.
Current compiled types and assumptions are checked by the registered
`generic_algebra`, `generic_consumer`, `relational_consumer` and
`generic_mdp` groups; their Gate M companions are audited separately.
See [Maintained verification](AUDITING.md) for commands and trust boundaries.
Historical stage reports are not current TODOs or current module/test counts.
