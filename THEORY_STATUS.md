# Maintained theory: status and limits

This is a status map, not another theorem manual or development log.
Use the [documentation index](docs/README.md) for current guides and linked
source owners. Historical proposals, checkpoints and per-run validation
records remain in Git; old counts are not current verification results.

## Established results

| Area | Current result | Important condition |
| --- | --- | --- |
| Behavioral theory | Stable hitting, pstruct/pstrong-to-peutt, heterogeneous bind and generic algebra | Explicit probability-level laws; structural bridges need relational limits |
| Iteration | Eventful relational congruence and full iteration_uniform | Relational zero/lub plus the proved scheduling/continuity profile |
| Frontier analysis | Generic complete-step iteration summaries; return-only Kleisli compatibility | Actual step certificates; no AST, no_event or finite-native-limit requirement |
| Least fixed points | Native MathComp and independent OmegaVal leastness; FreeOmega interpretation into the latter | Not leastness of every raw syntactic FreeOmega relation |
| pGCL forward semantics | Generic kernels and State elaboration; exact complete-frontier correspondence for native-parametric FreeOmega, instantiated for Q/R | Pure probabilistic fragment; no wp/validation dependency; order-theoretic leastness keeps genuine supremum premises |
| Interpretation | Public `interp = fold handle msample`, productive `interp_tree` agreement, handler algebra, State preservation | Target-specific laws and appropriate generic profiles; sampling selection is not a correctness axiom |
| ITree | from_itree_eutt_iff on the probability-free embedding's image | Separating probability laws, not an arbitrary positive lifting interface |
| MDP | Generic fragment coincidence and faithful source-kernel correspondence | Native/frontier reflection, total source rows and fragment support |
| External soundness | Native-parametric modelability, qlift bounded-test soundness, stable-hitting adequacy | Compatible interpretation into independent OmegaVal |
| Concrete external joints | General relational realization for modelable Q/R completions | Countable support; no arbitrary-native joint-existence assertion |
| Execution | Exact rational tickets, actual bounded replay law and hitting-limit correspondence | History-conditionally uniform ideal entropy; not a host-PRNG theorem |

[Generic theory](docs/THEORY.md), [iteration](docs/ITERATION.md),
[interpreters](docs/INTERPRETERS.md), [MDP](docs/MDP.md),
[external soundness](docs/FREEOMEGA_SOUNDNESS.md) and [execution](docs/EXECUTION.md)
give the claim boundaries. [Case studies](docs/CASE_STUDIES.md) points to actual
whole-program proofs rather than duplicating them here.

## Model and trust status

- SubEnumQ and SubEnumR share invariant-bearing finite containers and use
  observable FreeOmega as the complete frontier. Both instantiate the generic
  behavioral theory and have external complete-hitting modelability and joint
  realization. Finite native carriers are not required to be omega-complete.
- Raw EnumQ remains weighted analysis infrastructure, not an intrinsic
  subprobability carrier. Well-formedness does not imply termination.
- MathComp native order, omega/continuity, diagonal/Fubini and relational bind
  are normally checked. Its same-carrier recursive PTree assembly is permitted
  only in `Eq/Backend/MathComp.v` and `tests/MathComp.v` (Gate M), with local
  universe checking disabled. There is no MathComp + FreeOmega backend.
- MathComp composition retains `MathCompCouplingGluing`; stronger structural,
  eventful-iteration and unrestricted-interpreter consumers additionally keep
  unrestricted relational-lub explicit. Generic bind and MDP correspondence
  do not require that additional relational-lub premise.
- SubEnumR's native-reflection proof value is validation-owned and explicit,
  not an automatic mainline capability. Mainline reasoning never imports its
  own external validating model.

See [backends](docs/BACKENDS.md) and [architecture](docs/ARCHITECTURE.md).
Classical/extensional dependencies are recorded per compiled endpoint in
[the registry](tools/data/CONTRACT_SUITES.json). Conditional generic theorems
are not claims of constructive or assumption-free concrete instantiations.

## Deferred TODO

- **MonadSample transformer liftings — deferred:** add ReaderT, WriterT and
  ExceptionT liftings, reusing their existing explicit sampling algebras.
  PTree and StateT already have instances. This is future API work, not a
  blocker for the current interpretation; it does not include proving new
  transformer commuting laws. See [interpreter boundaries](docs/INTERPRETERS.md#remaining-boundaries).

## Remaining limits

The maintained artifact does not establish:

- unrestricted native MathComp relational-lub closure or unconditional gluing;
- arbitrary-target Reader/Writer fold commuting, all Conway/Elgot inheritance
  laws, or preservation by an arbitrary fold/sampling implementation;
- reconstruction of every syntactically Prob-free PTree as an ITree, or
  reflection for arbitrary handlers or probability-lowering elaboration;
- an additive probability interpretation for arbitrary raw non-increasing
  FreeOmega Lubs, syntactic qlift completeness, or arbitrary-native joint realization;
- reconstruction of every MDP-fragment tree as a source MDP;
- infinite-path measures, schedulers/conditioning, a general WP/temporal/metric
  theory, or strictness of transition inclusion for every abstract backend;
- end-to-end OCaml/PRNG probability correctness. Fuel-free extracted experiments
  are demonstrations, separate from the finite ideal-entropy theorem;
- a completed recursive whole-library kernel audit. Safe AllImports checks
  joint universe compatibility; targeted coqchk -norec trusts dependencies.
  Neither safe check includes Gate M as a universe-consistency result.

The ITree reverse bridge and full uniformity package are **proved**, not pending.
Auxiliary FiniteInternal/Recovery infrastructure stays maintained but is not
canonical semantics, another equivalence, or a dependency of the main peutt/
Interp route. See [verification](docs/AUDITING.md) for current commands;
local success never implies remote CI success.
