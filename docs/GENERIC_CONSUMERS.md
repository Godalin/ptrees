# Upper-layer consumer convergence

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

## Validation discipline

During development, compile changed owners and compare their actual types
and assumptions. Aggregate imports, the 465 maintained contracts, Gate M
contracts, tool tests and targeted joint kernel checks are consolidated at
the final convergence point. No whole-library universe-safe claim includes
the two existing Gate M modules.
