# Interpreted standard-effect algebra

Baseline: `6debbab`. This is the finite effect-algebra / probability-interaction
increment of the larger interpretation-framework proposal, **not completion
of that whole proposal**. Existing interpreters, transformer definitions,
ITree bridge, behavioral relations, routing and extraction stay unchanged.

## Scope and ownership

The new opt-in owners are `Interp/Algebra/{Computation,Reader,State,Writer,Exception}`.
They are generic in the native/frontier carriers and do not import FreeOmega,
MathComp, concrete backends or the external validation model. No facade export
order is changed. Old structural computation endpoints keep their old names
and types; qualify the new owner when both are imported.

Every effect equation is stated **after interpretation**. An uninterpreted
`Vis Get`, `Vis Ask`, `Vis (Tell unit)` or `Vis (Throw e)` remains observable.
No new source-level behavioral relation is introduced.

### Reader

- `run_reader_ask` evaluates a single Ask at the supplied environment.
- `run_reader_ask_ask` contracts repeated reads.
- `run_reader_prob` retains native sampling and the environment.
- `run_reader_ask_prob` commutes a read with a fixed sample, keeping both
  continuation arguments in their original roles.

The existing `StandardFacts.run_reader_bind` remains the structural bind law.
There is no new Local event, local operation, or ReaderT claim in this increment.

### State

`state_get_step` / `state_put_step` expose finite interpreted computation.
The four continuation-style laws are `run_state_get_get`, `run_state_get_put`,
`run_state_put_get`, and `run_state_put_put`. The generalized get-put law
restores the old state before running an arbitrary continuation.

`run_state_prob`, `run_state_get_prob` and `run_state_put_prob` preserve native
probability and justify read/fixed-write commuting conversions. Sampling may
be a subdistribution: no totality or probability/effect commutativity axiom
is used. The old `StateFacts.run_state_bind` is retained unchanged.

### Writer

Writer still means the existing `writer_handler` into State, followed by
`run_state` at the monoid unit. It has **not** been replaced by WriterT.

`run_writer_from` exposes exactly the same implementation at an arbitrary
initial log. Its tell equation computes `old_log <> newly_told_value`.

The structural bind law threads the accumulated log:

```text
run_writer_from op (t >>= k) log
  ≡p
run_writer_from op t log >>= fun (w,a) => run_writer_from op (k a) w
```

`run_writer_bind` specializes this at the monoid unit. This is an
accumulator-threading law, **not yet** an independent WriterT append/commuting
theorem. It requires no monoid laws or probability capabilities.

`run_writer_tell_unit` and `run_writer_tell_append` explicitly require
ExtLib `MonoidLaws`. No commutativity is assumed. `run_writer_tell_prob` only
moves a *fixed* log entry across sampling; it does not replace a
sample-dependent log with a fixed one. Its compiled signature does not need
`MonoidLaws` at all. `run_writer_prob` preserves each branch's own log.

### Exception

`run_exception_ret`, `run_exception_throw`, and `run_exception_throw_bind`
identify early exit with a returned `inl error`. `run_exception_bind` is
proved structurally by coinduction and uses the usual Except continuation:

```text
inl error -> Ret (inl error)
inr value -> run_exception (k value)
```

`run_exception_prob` leaves a native Prob in place. There is deliberately no
unconditional rule erasing a sample before Throw, no new Catch event, and no
new ExceptT implementation.

## Assumptions: actual compiled contracts

The elementary laws use observation equality and finite Tau elimination;
they do not invoke generic interpreter preservation or relational-lub closure.

- Exact observation equations need only the frontier operations/Core relation.
- Tau-eliminating equations add frontier Bind, Omega and constant/prefix
  cofinality laws. The unused native `SemanticMeasure` context drops out of
  their compiled signatures.
- Moving eliminated effects through Prob additionally consumes the existing
  native Core, mixed relational-bind, order and mixed-omega capabilities via
  `PEutt.peutt_prob_Proper`.
- Structural Writer/Exception bind laws have no probability capability premise.
- Writer unit/fusion retain their explicit monoid-law premise.

The generic `PEutt.peutt_prob` already depends on Coq
`RelationalChoice.relational_choice` and
`ClassicalUniqueChoice.dependent_unique_choice`. The four new probability
interaction theorems and their direct clients inherit these existing
dependencies, along with the existing dependent-inversion dependency.
They are **not axiom-free**. No new axiom is declared, and no baseline axiom
whitelist is widened: the audit bounds exactly these named consumers by the
frozen `peutt_prob` contract in `6debbab`. Other endpoints are checked against
the unchanged external-soundness whitelist. All 58 compiled types and
`Print Assumptions` outputs are in `EFFECT_ALGEBRA_CONTRACTS.json`.

## Tests and a real source program

`Regression/Semantics/EffectAlgebra.v` checks rational and finite-real clients,
a large result carrier, list-valued noncommutative logs, and exact ordered
output `[1;2]`. Writer unit/fusion work for that noncommutative monoid.

The semantic negative endpoint `sampling_before_throw_not_erasable` uses a
one-entry rational distribution of mass **1/2**. Both successful paths throw
the same error, but sampled-then-thrown error mass is 1/2 and immediate error
mass is 1. The proof uses actual complete-hitting witnesses and the existing
qlift mass theorem to refute `peutt`; it is not just an execution test.
The auxiliary `realType` argument supplies the scalar model for that existing
mass theorem, not a new probability axiom or a normalization premise.

`Examples/EffectInteractions.v` contains an actual ITree program with
`Sample`, `Get`, and `Put`, and proves:

```text
run_state (elaborate (count_sample mu)) n
  ≈p Prob mu (fun b => Ret (S n,b))
```

The distribution `mu` is arbitrary SubEnumQ, not necessarily fair or total.
The same program instantiates the existing StateT commuting square for an
arbitrary target with Monad laws, Eq1 equivalence and explicit
`iteration_uniform`. No inference from bare MonadIter is made.

## Remaining proposal work

This increment does not close these independent obligations:

1. General source `ITree.eutt -> peutt`, hence lowering preservation and the
   source-`ITree.interp` commuting square. The existing structural bridge and
   bind/iter laws remain available, but are not substitutes for weak simulation.
2. Canonical ReaderT/WriterT/ExceptT targets, their lawful iteration evidence,
   and their agreements with the existing PTree eliminators. StateT already
   has its checked theorem; it has not been generalized by assertion.
3. WriterT's accumulated-log iteration and append-form bind law; derived
   transformer `local` / `catch`, if included in the eventual public surface.
4. A general *conditional* sample-before-throw elimination theorem under an
   appropriate native totality/coupling hypothesis. The negative theorem here
   rules out the unconditional version, but does not prove that positive theorem.
5. Final facade selection and a consolidated full-framework audit.

In particular, Reader/Writer currently use `PTree.interp`, which inserts
administrative Tau around residual events. The exact one-step square used by
the direct State eliminator cannot simply be copied for these implementations.
The requisite target iteration laws must be proved/identified before stating
a generic transformer agreement theorem.

## Preservation gate

`audit_effect_algebra.py` reconstructs the frozen 382-module baseline exactly.
All old theory files are byte-for-byte unchanged except the seven sorted
AllImports additions. It rejects new capabilities, axioms, bypasses, global
hints/instances and concrete-backend imports in the generic owners. The prior
ITree/handler source audits consume an additive adapter, not relaxed baselines.
The existing contract snapshots are retained unchanged. CI is excluded.

Local verification completed:

- Full `opam exec -- dune build`, including safe AllImports and existing
  extraction targets (only the pre-existing extraction warnings).
- All 292 Python tool tests.
- Architecture, public surface and soundness source audits: 389 modules,
  387 Gate S and the same two Gate M.
- All 465 old compiled contracts unchanged; all 61 prior ITree bridge
  contracts unchanged; 58 new compiled types/assumptions checked.
- Joint `coqchk -norec` of all seven new safe module bodies, with the usual
  native-to-VM conversion fallback. Dependencies are trusted; this is not
  a recursive whole-library kernel audit and does not include Gate M.
- `git diff --check`.

No CI run was inspected or used as evidence; no environment was changed.
