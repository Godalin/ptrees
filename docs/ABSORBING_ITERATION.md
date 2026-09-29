# Ret/Vis absorption after unbounded internal retries

Baseline: `a39cf99`. This is a bounded extension of the accepted native-round
summary, not a replacement or an arbitrary eventful-frontier fixed-point theory.

This document records the staged profile accepted at `5431810`. The later
[generic complete-frontier bridge](FRONTIER_ITERATION.md) also supports
arbitrary MF-valued step frontiers and arbitrary frontier backends. Its
FreeOmega instance, `complete_iteration_hitting`, is in the same module.

## Interface and mathematical boundary

`Interp/FreeOmega/AbsorbingIteration.v` takes:

```
transition : I -> MN (I + B)
step       : I -> ptree E MN (I + B)
exit       : B -> ptree E MN A
exit_front : B -> FreeOmega MN (stable_head E MN A)
```

The local certificates are complete hitting of `step i` into the native
return-only kernel and complete hitting of `exit b` into `exit_front b`.
The exit frontier may contain **both Ret and Vis**, may have missing mass,
and need not be a native measure. The full visible continuation is retained.
Only the loop's per-round kernel still factors through MN.

`absorbing_iteration_summary` gives an **exact complete witness** for
`bind (iter step i) exit`. Its frontier binds the accepted `iteration_frontier`
to the exit frontiers on return heads. It is an unnormalized weighted
composition: no branch selection or conditional normalization occurs.

The proof uses `iteration_frontier_summary_hitting` and the already existing
`stable_hitting_bind_ret_only`. It contains no new primitive-fuel schedule,
cofinality proof, probability capability or semantic definition.

To obtain a loop which itself offers events, push the exit into successful
rounds using iteration naturality:

```
absorbing_step i := bind (step i) (fun next =>
  match next with
  | inl j => Ret (inl j)
  | inr b => bind (exit b) (fun a => Ret (inr a))
  end)
```

For **every** complete witness of `iter absorbing_step i`,
`absorbing_iteration_heads` supplies a lifting under `stable_head_rel eq peutt`
to the reference frontier; `absorbing_iteration_exists` also constructs the
existential hitting witness. Naturality preserves the behavior of visible
continuations, not their literal syntax. Therefore the pushed-in version is
deliberately not claimed to have the identical reference witness. This is one
whole-head coupling, not a separate coupling for each event response.

No AST, mass-one, finite-state or `no_event` premise is imposed. A native exit
descriptor `B` avoids placing recursive `stable_head` values inside MN; there
is no new universe bypass. This native-parametric theory remains explicitly
FreeOmega-qualified.

## Concrete supporting case

`Examples/AbsorbingFrontier.v` reuses the proved two-biased-toss VN round.
Each round retries with probability 5/9; the two successful descriptors have
mass 2/9 each. Repeated retries have no finite bound. Upon absorption:

- `false` returns `false`;
- `true` offers `Query`, retaining `fun answer => Ret answer` as continuation.

The final reference frontier samples a fair Boolean and contains
`FHRet false` and `FHVis Query (fun answer => Ret answer)` with equal weight.
`absorbing_program_rewrite` is the short full-program calculation: pull the
exit outside iteration, rewrite VN to direct fair sampling, and finish by
reflexivity. The existing VN convergence proof is reused, not duplicated.

`staged_frontier_exact` and `absorbing_round_frontier` instantiate the new
summary interface. `absorbing_first_frontier` relates any complete witness of
the actual eventful loop to the explicit fair mixed frontier. The reference
offered-event observation and its exact 1/2 probability are also proved;
this numeric lemma is explicitly about the reference measure, with the
whole-head lifting theorem providing the behavioral connection to the loop.

This is a supporting example, not a replacement for MixedHead or Adaptive.
The accepted VN, Adaptive, FactoryController and RandomWalk files are unchanged.

## Regression and assumptions

`Regression/Semantics/IterationFrontiers.v` checks that an offered event with
an empty response type still appears as a visible head, distinguishes two
such events, permits zero-mass kernels, and obtains a real hitting witness
for the pushed-in eventful loop on an unbounded nat state space.

The construction consumes existing native Core/AELift/CouplingAE/CountableAE
and Omega structure. It does not add classes or axioms. Compiled theorem
types and assumptions are recorded alongside the existing generic-algebra
contracts; all older contracts remain frozen.

The three new library theorems and the behavioral case endpoints depend only
on the already used dependent functional extensionality and `eq_rect_eq`.
The reference observation/probability lemmas are closed under the global
context. No choice dependency is introduced.

Out of scope **at that checkpoint**: arbitrary MF-valued retry kernels, an independent
Ret/Vis frontier iteration operator for arbitrary step trees, full generic-MF
abstraction, and forced migration of RandomWalk. This stage validates the
**absorbing-exit profile** using existing iteration and bind algebra.

## Local validation

- Full `opam exec -- dune build -j 2`, including AllImports and extraction.
- All 141 tool tests and architecture/API/soundness source checks.
- 465 original main contracts unchanged; 80 original generic-algebra
  contracts unchanged, plus 14 new exact type/assumption contracts.
- Joint `coqchk -norec` for the three new modules: AbsorbingIteration,
  AbsorbingFrontier and the absorption regression. This checks their bodies
  while trusting dependencies, not a recursive whole-library audit.
- No new universe relaxation; the two existing Gate M files and allowlist
  are unchanged. Full build is not claimed to be entirely universe-checked.
- CI was not inspected or used as an acceptance condition.
