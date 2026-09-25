# Upper-layer consumer convergence

## Current capability and model status

The stage reports below are historical, not a description of remaining work.
In particular their former FreeOmega-only structural/iteration boundaries
have since been generalized. See [generic structural consumers](GENERIC_RELATIONAL_CONSUMERS.md),
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
`relational_lub` certificate. All direct MathComp PTree clients remain in the
same two-file Gate M boundary. Native probability mathematics remains checked.

| Generic owner / endpoints | Probability requirements beyond chosen operations | FreeOmega over SubEnumQ / SubEnumR | MathComp direct |
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
exactly this small profile; the direct MathComp client has no L parameter.
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

### Local verification of this follow-up

- Full `dune build -j 4`, including AllImports: passed. This is a build
  result, not a claim that Gate M is universe checked.
- 125 tool tests, architecture `--check`, soundness source audit and the
  32-group contract registry metadata check: passed. No audit script or query
  group was added; module count remains 425, with the same two Gate M files.
- The 465 main contracts and 43 established MathComp direct/control contracts
  passed unchanged; their snapshot files were not refreshed.
- Selected compiled groups passed: generic algebra (18), relational consumers
  (54), relational direct clients (10), and iteration algebra (24).
  Only the existing generic left-unit contract changed; the three new entries
  cover observation equality and the two minimal-profile clients. All other
  entries in the edited snapshots were compared unchanged, including the
  FreeOmega left-unit wrapper and historical before-snapshots.
- Joint `coqchk -norec` passed for `Eq.Algebra`, `Eq.FreeOmega.Algebra`,
  `Interp.IterationAlgebra`, `Regression.Semantics.GenericAlgebra`, and
  `Regression.Semantics.PTreeIterationAlgebra`. This checks those five safe
  module bodies while trusting dependencies, not the whole library recursively.
  Gate M was excluded and retains its separately audited unsafe-hierarchy flags.
- No new semantic or logical axiom, canonical-routing change, or checker
  relaxation. Remote CI was not queried or changed.

## Historical convergence stages

Baseline: `c2dea6b` (accepted generic algebra stage). The user subsequently
authorized autonomous convergence, with targeted development checks and one
consolidated final regression run. CI and environment changes are excluded.

## Stage 2: structural bridges — the actual limit obligation

`GENERIC_CONSUMERS_BEFORE.json` records the compiled signatures and logical
assumptions before this work, not reconstructed source-level contexts.

The existing `peutt_of_pstruct` and `peutt_of_pstrong` require native measure
operations, native CoreLaws and native omega operations. Their frontier is
specifically the observable `FreeOmega MN`. They do **not** require native
omega completeness, countable AE, or commutativity. Both proofs have two
distinct ingredients:

1. Finite lockstep approximation: `ptree_hitting_pstruct/pstrong` construct
   structural liftings of corresponding finite approximants. The strong
   version consumes native relational lifting at probability nodes.
2. Relational limit closure: pointwise liftings of the two approximant chains
   become a lifting of their complete outputs through `FOQLLub` and equality
   transport.

The second ingredient now has a probability-owned derived theorem,
`Prob.FreeOmega.RelationalLimit.free_omega_lift_lub`. Both structural bridges
consume it; their statements remain unchanged. This removes duplicated
quotient-composition bookkeeping without modifying `qlift` or approximation.
The helper handles arbitrary representatives of the two observable lubs.

The actual missing generic proof obligation is of the following form:

```
increasing c, increasing d
lub c mu, lub d nu
(forall n, lift R (c n) (d n))
--------------------------------
lift R mu nu
```

Current `OmegaLaws.sem_lub_proper` concerns **same-carrier sem_eq**, not this
heterogeneous relational property. `sem_bind_lub` and diagonal/Fubini laws
concern limits of operations, not existence of related joints at limits.
The FreeOmega helper is even stronger (formal quotient lubs need no
increasing premise), but that strength is not imposed on other models.

No derivation of the displayed relational closure from the existing generic
profile is established here. This is a proof boundary, **not** a theorem of
logical independence or a claim that MathComp cannot satisfy it. In the
MathComp model, finite coupling composition/gluing does not by itself supply
the missing limit-of-couplings argument. No new law class, realization axiom,
external-domain dependency, or backend-specific copy of a PTree bridge is
introduced to hide that obligation.

Consequently the structural bridges and their six elementary FreeOmega
algebra consumers remain at their existing owners. Universalizing them by
assuming the desired PTree bridge would not count as progress.

## Stage 3: iteration has three different obligations

| Existing family | Actual dependency | Disposition |
| --- | --- | --- |
| Structural step/unfold/natural/codiagonal | `pstruct` theorem then structural bridge | Remains FreeOmega, for the Stage 2 limit reason |
| Behavioral step plus `no_event` | Complete-row construction, unbounded-step hitting, relational lub | Remains FreeOmega; no-event is a program restriction, not a backend capability |
| Eventful generator closure | Generic `peutt_coinduction` alone | Moved to `Eq.Iter` |

`iter_eventful_bisim_candidate`, `iter_eventful_generator_closed`, and
`peutt_iter_eventful_of_generator_closed` now have one generic owner. The
FreeOmega module exports that owner, not a duplicate proof or alias. The
compiled theorem needs only frontier measure/CoreLaws, mixed operations and
omega operations; neither native capabilities nor omega laws are necessary.
The proof is unchanged. The existing closure condition stays explicit and is
not promoted to a class or presented as arbitrary eventful step congruence.

`GenericConsumers.free_omega_eventful_iter` recovers the old specialization.
The already allowlisted MathComp direct regression instantiates the same
theorem. Both are conditional closure clients, not proofs that arbitrary
handlers/loop steps satisfy the condition. Generic-only imports also exclude
FreeOmega, MathComp and external validation.

## Stage 4: generic guarded interpretation, including scheduling

The interpreter chain now has generic owners:

```
Interp.Scheduling      finite approximation inequalities -> cofinality
Interp.Preservation    complete-head Vis fusion -> peutt preservation
Interp.Guarded         semantic visible guarding -> Vis fusion
```

Scheduling is not supplied as a new handler capability. The two finite
inequalities are proved from existing preorder-compatible ret/zero/mixed-bind
laws, reusing `Eq.BindScheduling`'s finite preorder algebra. Global fuel `n`
is covered by diagonal fuel `n`; split source/head fuel `(n,m)` is covered by
global fuel `n+m`. Directed cofinality then identifies their lubs. In
particular there is no assumption that observable `sem_eq` reflects `sem_le`.

The actual compiled profiles are:

| Generic endpoint | Requirements |
| --- | --- |
| `guarded_handler` | FI / MX / FO operations only |
| `guarded_handler_of_hitting` | frontier CoreLaws, OmegaLaws, CouplingAELaws |
| finite interpreter scheduling | OrderLaws, BindOrderLaws, MixedMeasureBindOrderLaws |
| interpreter cofinality | finite scheduling profile + DirectedCofinalityLaws |
| fusion -> preservation | generic bind profile (Stage 1) |
| guarded fusion / preservation / explicit Proper | preceding profile + frontier CouplingAELaws |

Thus generic guarded interpretation requires no native SemanticMeasure,
native CountableAE, commutativity, omega-Fubini, external model or FreeOmega
carrier. All new generic interpreter theorems are closed under the global
context. This does not say their concrete probability instances have no
logical dependencies.

The guarding definition still permits missing mass, arbitrary internal
computation and zero-mass return branches. The convenient-witness helper now
uses generic equality transport and CouplingAE rather than qlift-specific
support transport. The fusion proof enters the recursive candidate only
after a visible head, and preservation reuses generic up-to-bind coinduction.

The existing FreeOmega `Base`, `Cofinality` and `Guarded` endpoints become
explicit model specializations of these proofs. Their established statements
are retained, with no second coinduction/scheduling proof. The old specialized
predicates reduce to the generic definitions; this is intentional
specialization, not competing typeclass routing. `PTreeFacts` exports the
generic guarded owner directly instead of relying on export-order shadowing.
Atomic and MDP interpretation are not generalized or redesigned in this task.

Clients cover the existing SubEnumQ guarded suite, a SubEnumR completion
specialization, and direct MathComp. The latter constructs an actual guarded
heterogeneous handler `E -> F`, with `Tau; Vis; Ret`, and uses the same generic
preservation theorem on arbitrary related input trees. Its Tau rewriting
example is a consumer, not a MathComp copy of the proof. It remains in the
already allowlisted Gate M file, with gluing explicit.

## Convergence boundary

Completed: generic bind/fmap Proper (Stage 1), probability-owned relational
limit factoring, generic eventful closure, and the complete generic guarded
interpreter chain, including derived scheduling. No acceptance pause remains.

Not claimed: unrestricted eventful behavioral iter congruence, generic
structural-to-behavioral bridges, generic eventless complete-row theory,
arbitrary unguarded interpreter congruence, or generic Atomic/MDP consumers.
The first three boundaries are explicitly classified above; the last two are
not part of this extraction. In particular, a new relational-lub mathematics
project is not silently turned into an extra axiom just to move more files.

## Validation discipline

During development, compile changed owners and compare their actual types
and assumptions. Aggregate imports, the 465 maintained contracts, Gate M
contracts, tool tests and targeted joint kernel checks are consolidated at
the final convergence point. No whole-library universe-safe claim includes
the two existing Gate M modules.

Final local validation:

- Complete `opam exec -- dune build`, including safe AllImports and direct
  MathComp clients: passed.
- 160 Python tool tests: passed. An initially missing regression-inventory
  entry was fixed; the entire test suite was rerun successfully.
- Architecture/ownership and soundness source contracts: passed. There are
  319 modules: 317 Gate S and the unchanged two-file Gate M allowlist.
- Exact source conservation: 305 old modules remain byte-for-byte unchanged;
  the eight changed old modules are checked against explicit transformations.
- 465 compiled contracts: 464 exactly unchanged from `c2dea6b`; the one
  eventful iter theorem is relocated/generalized with a before/after ledger.
  Its old `eq_rect_eq` dependency disappears in the generic proof.
- 24 new compiled endpoints: checked, with the original logical-axiom
  whitelist. All generic Eq/Interp endpoints are closed under the global
  context. The FreeOmega relational-limit helper retains the existing
  concrete model's `eq_rect_eq` dependency.
- MathComp snapshot: all 39 old entries (33 direct endpoints and six safe
  controls) unchanged; four new direct clients added. Unsafe-hierarchy
  reports remain separate from logical assumptions, not suppressed.
- Joint `coqchk -norec` of 11 safe module bodies: passed. Targets are
  `RelationalLimit`, `Eq.FreeOmega.Relation`, `Eq.Iter`, `Eq.FreeOmega.Iter`,
  `Interp.Scheduling`, `Interp.Preservation`, `Interp.Guarded`, their three
  FreeOmega consumers, and `GenericConsumers`. Dependencies are trusted by
  `-norec`; this is not a whole-library recursive kernel audit. Gate M is
  excluded.

CI was neither inspected nor changed. No environment changes were made.
