# ITree embedding conservativity and interpreter compatibility

The probability-free embedding now preserves **and reflects** heterogeneous
weak equivalence. Generic proofs belong to `Interp/ITreeEutt.v` and
`Interp/ITreeReflection.v`; FreeOmega only discharges their probability laws.
No datatype, relation, interpreter, capability, canonical route, extraction
target, or MathComp trust boundary is changed.

## Current results

All principal proofs belong to generic `Interp/`, not a backend:

```text
from_itree_eutt:
  eutt RR t u
    -> peutt RR (from_itree t) (from_itree u)

from_itree_eutt_reflect:
  peutt RR (from_itree t) (from_itree u)
    -> eutt RR t u

from_itree_eutt_iff:
  eutt RR t u
    <-> peutt RR (from_itree t) (from_itree u)

interp_itree_eutt:
  eutt RR t u
    -> peutt RR (interp_itree h t) (interp_itree h u)

elaborate_eutt / elaborate_closed_eutt:
  source eutt RR -> native-probability lowering preserves peutt RR

from_itree_interp:
  from_itree (ITree.interp h t)
    ≈p PTree.interp (fun X e => from_itree (h X e)) (from_itree t)

interp_itree_source_interp:
  interp_itree g (ITree.interp h t)
    ≈p interp_itree (fun X e => interp_itree g (h X e)) t

elaborate_source_interp:
  elaborate (ITree.interp h t)
    ≈p interp_itree (fun X e => elaborate (h X e)) t
```

Preservation is genuinely heterogeneous in return carriers `A/B` and `RR`.
The source handler may immediately return, diverge, or perform multiple
visible events. No visible-first, atomicity, AST, or totality premise is
introduced. `elaborate_eutt_Proper` is an explicit lemma for local registration;
there is no new global instance or hint.

`Interp/FreeOmega/ITreePreservation.v` only supplies existing completion
certificates, including `free_omega_from_itree_eutt_reflect` and
`free_omega_from_itree_eutt_iff`. Rational and finite-real clients use those
same proofs, with no explicit extra hypothesis at the concrete endpoint.

This justifies the precise claim:

> On probability-free embedded ITrees, PTree weak equivalence coincides with
> ITree eutt, for the stated separating probability profiles.

The claim is about the **image of `from_itree`**, not an independently
defined subtype of all syntactically probability-free PTrees. There is no
`to_itree`, `prob_free` certificate, surjectivity or reconstruction theorem.
It is also **not** an iff for `interp_itree` or `elaborate`: an arbitrary
handler, especially probability lowering, can identify different source
visible behaviors. Those operations retain their preservation theorems.

## Why the weak embedding proof is sound

`itree_head_at n` searches through at most `n` source Taus for the first Ret
or Vis. `eutt_head_at` proves finite head correspondence by induction on that
budget and the inductive stuttering layer of ITree's eutt generator. Related
visible heads retain eutt-related **whole continuations**.

For `from_itree_eutt`, classical case analysis separates:

- a finite head: both embeddings have Dirac complete-hitting witnesses,
  related at their heads and recursively at visible continuations;
- no finite head: both finite hitting chains are zero, hence both complete
  witnesses are zero.

Only the final visible continuations re-enter PTree coinduction. Endless Tau
is not used as an observable guard, and no divergence is equated with Ret.
There is no countability, source termination, or native sampling premise.

## Why reflection is sound

Given `peutt` between embedded trees and a finite source head, its complete
frontier is a Dirac. If the other source had no finite head, its complete
frontier would be zero. Coupling-AE transport, zero-AE and exact Dirac-AE
would then imply `False` at the Dirac point. Hence the other source also
reaches a finite head. `sem_lift_ret_inv` extracts the related Ret/Vis heads
from their Dirac lifting; related visible continuations retain `peutt`.

`itree_head_at_eqitF` removes both finite Tau prefixes by induction and
reconstructs ITree's weak-bisimulation generator. Only the matched Vis
continuations use the recursive candidate. If neither source has a finite
head, `itree_no_head_eutt` matches their endless Tau behavior directly.

Reflection therefore needs **existing separating laws**, beyond the weak
algebra sufficient for preservation: coupling-AE, exact Dirac-AE and
omega-AE (for zero). An abstract interface whose lifting equates every
measure cannot support conservativity. The generic signature does not
hide this issue behind a backend name or a new theorem-shaped capability.
It requires no native measure laws, order, relational-lub continuity,
diagonal/Fubini, finite support, termination, external OmegaVal model or
choice. The combined iff additionally uses preservation's relational-zero
certificate.

The MathComp probe in `tests/MathComp.v` instantiates the **same generic iff**
with `MN = MF`, retaining its explicit `MathCompCouplingGluing` premise.
Only this already-allowlisted recursive-frontier client is Gate M; the
new generic proof and the SubEnumQ/SubEnumR clients remain Gate S.

## Source interpretation is a separate square

ITree places its administrative Tau **after** a handler; PTree places it
**before**. `ITreeSourceInterp.v` reconciles these schedules using a proof-only
ITree scheduling variant `itree_interp_before`:

1. ITree weak coinduction relates that variant to the original ITree interp.
   The candidate includes an active-handler phase. A returned handler matches
   the pending Tau; a visible handler enables the stronger guarded up-to rule.
2. Its embedding is structurally related to the unchanged PTree interp.
3. The new source-eutt theorem and existing generic structural bridge compose
   these results. Arbitrary target interpretation then uses the existing
   unrestricted handler preservation theorem.

This auxiliary scheduling definition is not exported through a public
aggregate and is not used by the actual elaboration/runtime implementation.
Its source equivalence and structural embedding proofs are axiom-free.

This is **not** merely the older target-handler postcomposition theorem.
The left side contains the actual upstream `ITree.Interp.Interp.interp`.
For sampling handlers, the source-square regression starts from ITree
sampling events and ends in native PTree probability.

An important boundary remains semantic, not a missing proof: a source
handler may rewrite `Sample mu`, whereas an ordinary PTree handler cannot
rewrite native Prob. Thus a square phrased as "first lower, then handle only
ordinary events" must require sample preservation. The general theorem
above instead lowers the **entire source handler** and makes no false claim
that arbitrary sampling changes commute with already-lowered Prob.

## Actual assumptions (compiled, not inferred from Section text)

| Endpoint | Probability requirements | Logical dependencies |
| --- | --- | --- |
| `from_itree_eutt` | MF Core/Bind, Mixed operations, omega/cofinality, relational zero | `Classical_Prop.classic` only |
| `from_itree_eutt_reflect` | MF Core/Bind, Mixed operations, omega/cofinality, coupling-AE, Dirac-AE, omega-AE | classic and `eq_rect_eq` |
| `from_itree_eutt_iff` | union of preservation and reflection | classic and `eq_rect_eq` |
| `from_itree_interp` | additionally generic structural-bridge native Core, order, relational mixed bind/lub | classic and inherited `eq_rect_eq` |
| `interp_itree_eutt`, lowering preservation | existing unrestricted-interp order/diagonal/Fubini/bind-order/directed-cofinality/selection and relational-lub profile | classic only at generic endpoints |
| `interp_itree_source_interp` | union of the two preceding profiles | classic and inherited `eq_rect_eq` |

In particular the generic embedding results need **no native measure laws,
no order laws, no relational-lub closure, no diagonal/Fubini, and no choice**.
The classical split is explicit. Reflection's `eq_rect_eq` arises in the
dependent inversion of related visible heads; the no-head eutt helper is
axiom-free. These proofs are not advertised as an axiom-free weak embedding.
No new logical axiom is declared, and the existing
logical-axiom whitelist is unchanged. Backend clients inherit their already
recorded dependencies; the two new FreeOmega endpoints additionally inherit
`FunctionalExtensionality.functional_extensionality_dep` from their profile.

`ITREE_PRESERVATION_CONTRACTS.json` retains its original 52 entries unchanged
and appends the four generic/FreeOmega reflection and iff endpoints, with
their actual compiled types and full assumptions. It uses the existing
contract runner, not a new stage-specific audit script.

## Examples and checks

The new regression checks heterogeneous returns with asymmetric finite Tau
prefixes; an infinite source interaction service with extra Taus every round;
pure silent divergence and no finite head; source divergence not eutt to Ret;
returning, diverging and two-query source handlers; sampling source handlers;
zero-mass native lowering; actual local setoid rewriting; SubEnumR clients;
and a return carrier strictly above Set. The same example file now checks
both directions for SubEnumQ/SubEnumR, reflected infinite interaction,
embedded divergence versus return, distinct returned values, and an offered
event with an empty response type versus divergence. The high-universe
client now includes the iff. Generic imports do not load a FreeOmega
backend, external OmegaVal validation, or Gate M.

The root build includes these examples and the separate Gate M probe.
Current architecture, source-safety and compiled-contract audits enforce
the dependency/trust boundary; historical migration replay scripts are not
part of the checking workflow. See `CONTRACT_SUITES.json` for the maintained
`itree_bridge` and `itree_preservation` groups. The latter records no claim
of reflection for arbitrary probability-lowering handlers.

Eventful iteration is separately covered by the generic handler machine;
see [eventful iteration](EVENTFUL_ITERATION.md). The new reflection theorem
does not change or depend on that argument.

## Local verification of the reflection follow-up

Starting from `7c11869`, the full root `dune build -j 2` (including AllImports
and extraction) and all 140 tool tests pass. Architecture and source-safety
checks cover 435 modules, with the same two exact-allowlisted Gate M files.
The 491 main, 61 bridge, original 52 preservation, 266 API owner/helper and 43 MathComp
contracts retain their types and assumptions; the extended preservation
group now checks 56 entries. No new audit script, probability capability,
axiom declaration, global instance or global hint is introduced. Remote CI
is not part of this validation.

Joint `coqchk` with a separate `-norec` for each of `Interp.ITreeReflection`,
`Interp.FreeOmega.ITreePreservation` and `Examples.Effects.ITreePreservation`
passes. This checks those three Gate S module bodies and trusts their compiled
dependencies; it is not a whole-library recursive kernel check. The MathComp
iff probe separately reports `unsafe_hierarchy` and collapsed session universes,
as expected, with logical axioms remaining inside the existing whitelist.
