# Standard effect clients

Baseline: `081ee41`. The six new modules reuse ITree's `readerE`, `writerE`
and `exceptE`; there is no new Events namespace or alternative event family.
The State and arbitrary-handler foundations and all backend definitions are
unchanged.

## Reader

`Interp/Reader.v` provides `ask`, `reader_handler`, and `run_reader`.
Ask returns the supplied immutable environment; remaining events are
forwarded. This is an ordinary fixed-handler `PTree.interp` client, with the
interpreter's existing administrative Tau behavior. Native Prob nodes are
never converted into visible effects.

`StandardFacts.run_reader_peutt` is one application of the arbitrary-handler
theorem, with arbitrary return relation and residual effect signature.
The structural Ret/bind equations reuse existing structural interpreter laws.

## Writer

`Interp/Writer.v` provides `tell`, `writer_handler`, and `run_writer`.
It uses the existing ExtLib `Monoid` operations and translates Tell into
standard Get/Put before running the existing State interpreter:

```
log := monoid_plus old_log newly_told_value
```

This fixes accumulation order. Preservation itself requires only those
operations, not associativity or commutativity: no regrouping or permutation
of writes is performed. Additional monoid-algebra rewrites would require
the existing `MonoidLaws`; they are not implicitly assumed here.

`StandardFacts.run_writer_peutt` composes arbitrary-handler preservation and
State preservation. Its output relation requires equal logs and the supplied
relation on results. There is no Writer-specific coinduction or probability
proof.

## Exception

ITree's `Throw err` returns `void`. A normal handler of type
`exceptE Err X -> ptree E MN X` cannot return an error to the entire caller:
it would have to produce a value of `void`. Therefore early exit is correctly
implemented as a result-changing transformation:

```
run_exception : ptree (exceptE Err +' E) MN A -> ptree E MN (Err + A)
```

Normal Ret becomes `inr`; Throw becomes `inl`; Tau, residual Vis, and native
Prob are preserved. Throw stops the computation and does not inspect an
impossible continuation. An error is a returned observable value, **not**
missing mass, divergence, or timeout.

`ExceptionFacts.v` maps complete stable heads: ordinary returns and thrown
events become result heads, while residual events keep recursively transformed
continuations. It proves equality in approximation order at **the same fuel**
between transformed-tree approximants and mapped source approximants. Existing
bind continuity and directed cofinality lift this to complete hitting.
Whole-frontier coupling then proves heterogeneous `run_exception_peutt`.
Errors must be equal; successful results use the supplied relation.

Unlike arbitrary internally returning handlers, this transformation never
resumes the source continuation after a handled event, so no collapsed-event
loop must be solved. Accordingly its theorem needs no relational-lub,
diagonal/Fubini, or omega-selection premise. It uses existing Core/order/omega,
bind and mixed order laws, directed cofinality, and relational bind. The generic
proof has no new logical or semantic axioms.

## Concrete checks

`Regression/Semantics/StandardEffects.v` checks generic import isolation and
heterogeneous preservation for all three clients. It also actually executes:

* Reader lookup followed by a native rational coin;
* Writer's two coin-dependent branches, producing `[1;2]` or `[1;3]` in
  chronological order;
* success and thrown-error branches of the same sampled program;
* missing mass, which still produces `Lost`, not an exception;
* residual event forwarding without changing its payload.

An unbounded probabilistic program with residual Vis and eventual Throw is a
weak-equivalence client, not merely a finite execution test. The executable
runner still has its documented fuel/entropy boundaries; these tests do not
claim a new uniform sampling theorem.

## Scope and verification

The source audit freezes all 351 preceding theory modules and five preceding
contract snapshots. It rejects redefined standard signatures, capability
assumptions, backend leakage, checker bypass, and loss of native Prob or
returned-error behavior. The new snapshot covers 31 compiled endpoints;
generic endpoints must be closed under the global context. The Exception
signature is additionally checked not to acquire the stronger collapsed-loop
limit capabilities.

This finishes the small standard-effect client group, not a complete effect
algebra. Subsequent increments prove [StateT-fold commutation](STATE_FOLD.md)
and [general rational single-draw correctness](RATIONAL_TICKETS.md), and add
the [extracted rewrite example](STATE_REWRITE.md). Whole-runner probability
correspondence remains open; see the [current roadmap](EFFECTS_EXECUTION.md#current-status).
The validation below is the historical result for this stage.

Local verification passed: full `dune build` (including AllImports), 39 focused
tool tests, architecture and soundness source audits, the 31 new compiled
contracts, and unchanged operational/handler/State contracts (44/27/28).
Joint six-module `coqchk -norec` passed: it checks selected safe module bodies
while trusting dependencies, not a recursive whole-library audit or either
MathComp Gate M file. No CI or environment change is included.
