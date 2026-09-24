# Exception transformer and fold agreement

Baseline: `9431e4b`. This additive increment completes the canonical ExceptT
fold/commuting slice of the interpretation-algebra proposal. It does not
complete ReaderT, WriterT, or the source-ITree weak-equivalence bridge.

## Standard transformer, explicit laws

The carrier and operations are the existing ExtLib `eitherT Err T`,
`Monad_eitherT`, and ITree `MonadIter_eitherT`. There is no new exception
transformer datatype, probability class, or global instance.

`Core/ExceptT.v` supplies opt-in constructors:

- `exceptT_eq1`: observe the underlying `T (Err + A)` computation.
- `exceptT_eq_equivalence`: inherit the base equivalence.
- `exceptT_monad_laws`: inherit `MonadLawsE`, including bind Properness.
- `exceptT_iteration_uniform`: inherit pure-map uniformity from the base
  iterator, using the base monad laws. It proves a law of ITree's existing
  transformer iterator, rather than assuming a transformer-specific law.

Errors terminate iteration; successful `inl` values continue and successful
`inr` values return. No extensional function/record equality is required.
All these constructions remain universe-checked and universe-polymorphic.

## Interpreter square

`Interp/ExceptionFold.v` defines separate algebras:

```text
Throw error  -> ret (inl error)
residual e   -> handle e >>= fun x => ret (inr x)
native mu    -> sample mu >>= fun x => ret (inr x)
```

`fold_exception` runs the ordinary generic fold into `eitherT`, then exposes
its `T (Err + A)` result. It does not replace the existing `run_exception`.

The principal theorem, in `Interp/ExceptionFoldFacts.v`, is:

```text
fold_exception handle sample t
    =eq1
fold handle sample (run_exception t)
```

Its compiled premises are exactly: base Monad and MonadIter operations,
Eq1 and its equivalence laws, MonadLawsE, and `iteration_uniform`.
`handle` and `sample` are arbitrary algebras. No SemanticMeasure, native
totality, FreeOmega, relational-lub, or MathComp premise occurs.

The proof exposes the actual transformer iteration step, proves its one-step
square using `observe_run_exception` and monad laws, and applies uniformity
with `h := run_exception`. In particular, the Throw case terminates on both
sides. It does not require an arbitrary-event interpreter preservation
theorem, a peutt assumption, or a second copy of the interpreter.

This is equality of two fold constructions under the *same* supplied sampling
algebra. It is not a claim that every supplied sampler is probabilistically
correct, or that every fold preserves peutt.

## Checked clients and boundaries

`Regression/Semantics/ExceptionFold.v` instantiates both transformer laws and
the square with actual ITree execution, using the previously proved
`itree_iteration_uniform`. It checks:

- Throw produces `Ret (inl error)`.
- Prob is executed by the separate sampling algebra.
- Sampling then throwing retains `sample >>= fun _ => Ret (inl error)`;
  sampling is not erased. The previous half-mass negative theorem in
  `EffectAlgebra` remains unchanged.
- A coinductive service offers a residual Request, then samples and may retry
  without bound, return, or throw. The full transformer square applies to it.
- A return carrier strictly above Set is supported.
- Loading this theory does not load peutt, FreeOmega, or OmegaVal.

The generic files are opt-in; no public facade export or theorem owner is
changed. The current Reader/Writer administrative-Tau obligations remain
open, as do source `ITree.eutt` preservation and the source-interp square.

## Verification and conservation

`audit_exception_fold.py` reconstructs all 389 baseline theory modules
byte-for-byte, except for four precisely identified sorted AllImports
additions. Earlier source audits consume the reconstruction adapter, without
relaxing their frozen snapshots. The new audit forbids new axioms/classes,
checker bypasses, global instances/hints, and probability-model dependencies.

The 24-entry compiled snapshot records types and `Print Assumptions`.
Every new endpoint is closed under the global context: **no logical axioms**.
The audit rejects even the previously whitelisted classical axioms here.

Local validation completed:

- Full `opam exec -- dune build`, including safe AllImports and the existing
  extraction targets (only pre-existing extraction warnings).
- All 300 Python tool tests.
- Architecture, public-surface and soundness source audits: 393 modules,
  391 Gate S and the unchanged two Gate M.
- All 465 mainline compiled contracts and all 58 prior effect-algebra
  contracts unchanged; 24 new compiled contracts checked.
- Joint `coqchk -norec` on the four new safe modules. Dependencies are trusted;
  this is not a recursive whole-library kernel audit and excludes Gate M.
- `git diff --check`.

CI was deliberately not inspected; the environment and MathComp Gate M are
unchanged. Existing contract snapshots were not regenerated.
