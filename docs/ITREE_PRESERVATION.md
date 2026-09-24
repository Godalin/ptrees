# Source ITree weak equivalence and interpreter compatibility

Baseline: `d79caca`. This additive increment closes the two source-bridge
obligations identified after the ReaderT/WriterT checkpoint. It does not
modify any existing datatype, relation, interpreter, probability capability,
canonical route, extraction target, or MathComp trust boundary.

## New results

All principal proofs belong to generic `Interp/`, not a backend:

```text
from_itree_eutt:
  eutt RR t u
    -> peutt RR (from_itree t) (from_itree u)

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
certificates. Rational and finite-real clients use those same proofs.

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
| `from_itree_interp` | additionally generic structural-bridge native Core, order, relational mixed bind/lub | classic and inherited `eq_rect_eq` |
| `interp_itree_eutt`, lowering preservation | existing unrestricted-interp order/diagonal/Fubini/bind-order/directed-cofinality/selection and relational-lub profile | classic only at generic endpoints |
| `interp_itree_source_interp` | union of the two preceding profiles | classic and inherited `eq_rect_eq` |

In particular the basic embedding theorem needs **no native measure laws,
no order laws, no relational-lub closure, no diagonal/Fubini, and no choice**.
The classical split is explicit; this increment is not advertised as an
axiom-free weak embedding. No new logical axiom is declared, and the existing
logical-axiom whitelist is unchanged. Backend clients inherit their already
recorded extensionality/choice dependencies.

`ITREE_PRESERVATION_CONTRACTS.json` records 52 compiled declarations and their
full assumptions. Previously frozen snapshots are not regenerated.

## Regression and preservation

The new regression checks heterogeneous returns with asymmetric finite Tau
prefixes; an infinite source interaction service with extra Taus every round;
pure silent divergence and no finite head; source divergence not eutt to Ret;
returning, diverging and two-query source handlers; sampling source handlers;
zero-mass native lowering; actual local setoid rewriting; SubEnumR clients;
and a return carrier strictly above Set. Generic imports do not load a
FreeOmega backend, external OmegaVal validation, or Gate M.

`audit_itree_preservation.py` freezes all 402 previous theory modules byte
for byte, permitting only the five exact sorted aggregate additions. It
checks generic ownership, source relation entry, genuine source interp,
unrestricted handler scope, regression boundaries, no new capabilities,
and no checker bypass or global inference machinery. Older additive audits
consume this adapter and retain their original snapshots.

## Remaining work

The next substantive theoretical question is arbitrary **eventful behavioral
iter congruence**. This increment proves source eutt congruence and source
interp compatibility; it does not turn the existing PTree generator-closure
iteration theorem into unconditional behavioral step congruence.

Arbitrary-target Reader/Writer commuting, optional local/catch/listen/pass,
and further public export selection remain deferred. No CI work is included.

## Local verification

- Full `opam exec -- dune build`, including safe AllImports and existing
  extraction targets (only the pre-existing extraction warnings).
- All 317 Python tool tests.
- Architecture, API and source-soundness audits: 407 modules, 405 Gate S
  and the same two Gate M modules.
- All 465 retained compiled contracts and 266 public owner/helper contracts
  unchanged; previous 59 ReaderT/WriterT contracts rechecked unchanged.
- All 52 new compiled contracts and their logical dependencies checked.
- Joint `coqchk -norec` of the five new safe module bodies.
- `git diff --check`.

The kernel check trusts compiled dependencies; it is not a recursive
whole-library audit and makes no claim about checking Gate M. No remote CI
was queried, changed, awaited, or counted as evidence.
