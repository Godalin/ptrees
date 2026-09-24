# ReaderT / WriterT interpretation-algebra checkpoint

Baseline: `2d59640`. This completes the Reader/Writer transformer operations,
monad laws, uniformity inheritance, and **actual ITree-target** fold agreements.
It does not claim arbitrary-target commuting from bare MonadIter or even from
uniformity alone. See the consolidated [scope table](INTERPRETATION_ALGEBRA.md).

## Generic transformer mathematics

`Core/ReaderT.v` reuses ExtLib `readerT` and ITree `MonadIter_readerT`.
Equality is pointwise in the fixed environment. Monad laws are inherited
from the base monad; iteration uniformity is inherited pointwise.

`Core/WriterT.v` uses the existing ITree `Monads.writerT W T = T (W * A)`
carrier. ExtLib's WriterT is value-first, so its operations are deliberately
not attached to this log-first carrier. We supply explicit operations:

```text
ret a       = ret (unit,a)
t >>= k     = t >>= fun (w,a) =>
              k a >>= fun (v,b) => ret (w <> v,b)
iter step i = base_iter
                (fun (w,i) => step i >>= fun (v,next) =>
                   ret (continue-or-return (w <> v) next))
                (unit,i)
```

Logs accumulate in execution order. Monad laws require ExtLib `MonoidLaws`;
commutativity is never required. The proof of iteration uniformity explicitly
uses base uniformity with the state map `(w,i) |-> (w,h i)`. It derives the
law for the concrete accumulator iterator, rather than assuming Writer
interpretation preservation as a new capability.

All operations, equality structures, and law constructors are opt-in
definitions/theorems, not global instances. Because `Monads.writerT` is a
transparent type alias, explicitly selecting `writerT_monad` at call sites
avoids ambiguity with the underlying monad. No inference hints are added.

`Interp/ReaderFold.v` and `WriterFold.v` provide the actual transformer folds:

- Ask returns the fixed environment; residual events use the supplied handler.
- Tell returns its log entry; residual events contribute the monoid unit.
- Reader sampling ignores the environment.
- Writer sampling lifts with an empty log, preserving the whole supplied
  computation. It does not erase a missing-mass/divergent sample.

`WriterFoldFacts.writer_fold_step_normalize` is generic over the base monad.
It proves that the transformer fold's accumulated one-step computation is
exactly the expected Ret/Tau/Tell/residual-Vis/Prob machine, modulo base Eq1.

## Actual execution-target agreements

`Interp/FoldITree.v` proves strong computation and bind equations for the
existing separate-Vis/Prob fold into ITree. Its proofs retain iteration's Tau
at recursive steps. This supplies legitimate coinduction guards even when a
handler returns immediately; it does not assume that a Vis handler itself
must be productive or guarded.

The paper-facing agreements are:

```text
itree_fold_run_reader:
  fold_reader handle sample t env
    ≈eutt fold handle sample (run_reader t env)

itree_fold_run_writer:
  fold_writer op handle sample t
    ≈eutt fold handle sample (run_writer op t)
```

Reader's existing implementation is still `PTree.interp reader_handler`.
Writer's existing implementation is still the State-based handler followed
by `run_state`. No old interpreter, event signature, or equation is changed.

The commuting proofs account for administrative Tau explicitly:

- Reader residual Vis has an extra pre-handler Tau.
- Writer Tell runs the existing Get/Put expansion, with its administrative
  steps; the proof computes those steps while keeping a matched iteration
  guard before recurring.
- The weak up-to-Tau reasoning is ITree's checked machinery. These proofs
  are not recycled as purported arbitrary-target uniformity proofs.

Writer is first proved for an arbitrary initial accumulator. A separate
`itree_writer_prefix` proves that prefixing the initial log equals prefixing
the final log. Combined with accumulator-threading bind, this yields the
canonical **append-form** `itree_writer_fold_bind`, not merely the older
State-threading equation. Reader also has strong Ret and bind laws. Thus both
folds preserve Ret/bind in their actual transformer targets.

The supplied sampling algebra remains arbitrary. These are equalities of
two executions with the same algebra, not proofs that every sampler is
probabilistically correct or that arbitrary fold preserves peutt.

## Regression and assumptions

`Regression/Semantics/ReaderWriterFold.v` checks inherited monad/uniformity
laws with ITree, actual Reader/Writer commuting, and append-form bind.
The Writer uses noncommutative list logs and computes `[1]` then `[2]` as
`[1;2]`. Recursive clients contain residual Tick, native Prob, unbounded Tau
retry, and either Ask or Tell. Both commuting theorems support carriers
strictly above Set. The theory does not load peutt, FreeOmega, or OmegaVal.

All 59 new compiled endpoints are closed under the global context: no logical
axioms. Generic modules have no probability/backend capability requirements;
the Writer endpoints retain their explicit `MonoidLaws` premise. Actual
commuting signatures explicitly contain `itree F`, rather than concealing
a target-specific proof behind a generic statement.

## Conservation and validation

All 393 baseline theory modules are byte-for-byte frozen except nine exact,
sorted AllImports insertions. `audit_reader_writer_fold.py` checks this and
the new compiled types/assumptions. Older audits reconstruct their baseline
through an additive adapter; their snapshots are not regenerated. No public
facade, backend, semantic relation, extraction code, or Gate M file changes.

Local validation completed:

- Full `opam exec -- dune build`, including safe AllImports and existing
  extraction targets (only the pre-existing extraction warnings).
- All 308 Python tool tests.
- All 465 retained main contracts and 24 prior ExceptT contracts unchanged;
  59 new compiled types and axiom-free assumptions checked.
- Public-surface audit: all 266 owner/helper and 25 capability contracts
  remain covered, with retained compiled contracts unchanged.
- Architecture and soundness source audits: 402 modules, 400 normally
  checked Gate S modules and the same two Gate M modules.
- Joint `coqchk -norec` on all nine new modules. Dependencies are trusted;
  this is not a recursive whole-library audit and excludes Gate M.
- `git diff --check`.

CI was not inspected and the environment is unchanged.
