# Full PTree iteration uniformity via a direct restart machine

Baseline: `88e9cf2`. This additive increment resolves the protocol-specific
universe obstruction to packaging full `iteration_uniform`. It does not
change PTree syntax, iteration, Eq1, any probability interface or canonical
routing. It adds no checker relaxation or global instance.

## Result and actual consumers

Explicit imports:

```coq
From PTree.Interp Require Import IterationUniform.
(* Canonical completion specialization: *)
From PTree.Interp.FreeOmega Require Import IterationUniform.
```

`ptree_peutt_iteration_uniform` proves the **complete** existing interface,
not a theorem with separately fixed small carriers. Its specialization
`free_omega_ptree_iteration_uniform` supplies existing probability certificates.
For an arbitrary pure map `h : I -> J`, the law is:

```text
forall i, bind (f i) (Ret o iteration_map h) ≈ g (h i)
-----------------------------------------------------
forall i, iter f i ≈ iter g (h i)
```

No injectivity, termination, no-event or generator-closure premise is added.
The underlying `peutt_iter_direct_rel` supports heterogeneous state and return
relations, including arbitrary visible interaction.

`Regression/Semantics/PTreeUniformity.v` exercises the full package with:

- the unchanged `fold_run_state` and `fold_run_exception`, using an actual
  PTree target, arbitrary source sampling carrier, handler and sampler;
- the unchanged ReaderT/WriterT/ExceptT uniformity inheritance theorems;
- both SubEnumQ and SubEnumR completion profiles;
- a whole PTree as loop state, and carriers strictly above Set.

These are checked together after importing safe AllImports. Writer needs
ordinary MonoidLaws, not commutativity. The fold squares compare the same
handler/sampler along two paths; they do not assert arbitrary samplers are
probabilistically correct.

## Why this avoids the obstruction

The old proof encoded `I+A` as the response of a synthetic Vis event. This
forced loop carriers into the event-response universe and prevented using
that proof at the entire input universe of monomorphic Eq1. Its negative
regression remains unchanged and continues to detect that precise failure.

The new machine keeps an active `ptree E MN (I+A)` as its semantic state:

```text
Ret (inl i) : restart at step i, consuming an internal step
Ret (inr a) : expose the stable return a
Tau t      : continue internally at t
Prob mu k  : take the native probabilistic transition
Vis e k    : expose e with residual iterated continuations
```

There is no synthetic event, new datatype, cofixpoint or alternative tree
representation. The existing `stable_target` separates restart states from
stable observations. In particular, carrying a whole tree as loop state no
longer asks that tree type to serve as a Vis response.

## Adequacy, not just a new proof candidate

`iter_active step t` is the actual PTree bind with return continuation
`inl i ↦ Tau (iter step i)`, `inr a ↦ Ret a`.

`iter_primitive_tree` relates the machine's finite approximant at fuel n
to the actual tree's hitting approximant at **the same fuel n**. The relation
is two-sided order comparison, not an assumed `sem_eq -> sem_le` reflection
and not claimed to be literal equality of measure representatives.

Complete-step acceleration uses a grid: n restart-machine steps, each with
m primitive internal steps. Both cofinal bounds are proved:

```text
grid n m <= primitive ((n+1)*(m+1))
primitive n <= grid n n
```

Existing directed-cofinality, bind continuity and diagonal/Fubini laws then
connect the grid to the complete-head restart kernel. The endpoint
`iter_machine_hitting_sound` sends every complete machine hitting witness
to an actual PTree stable-hitting witness.

Relational congruence couples those complete step frontiers using the input
`peutt` evidence. Related retry heads invoke the step hypothesis; exits use
the return relation; visible heads put their residual computations back
in the candidate. Existing `stable_hitting_rel` and the proved adequacy
close the coinduction. Finally the existing structural return-map lemma
turns a commuting pure-map square into the graph relation needed by full
uniformity. No desired conclusion is repackaged as an assumption.

## Probability and logical assumptions

The direct heterogeneous theorem needs frontier Core/Bind/order/omega,
cofinality, diagonal/Fubini, bind-order, mixed-bind-order, directed
cofinality, omega selection, `relational_zero` and `relational_lub`.
It does **not** need a native SemanticMeasure or `relational_mixed_bind`.
Native Core and the latter certificate enter full uniformity only through
the existing structural return-map bridge.

All machine endpoints and the direct relational congruence are closed under
their explicit contexts. The generic full uniformity theorem inherits only
existing `Eqdep.Eq_rect_eq.eq_rect_eq`. The FreeOmega specialization also
inherits functional extensionality; SubEnumR retains its existing classical
native foundations. No logical-axiom whitelist is enlarged. Complete compiled
types and assumptions are in `DIRECT_ITERATION_CONTRACTS.json`.

The same generic theorem is instantiated in the existing MathCompDirect
regression, still conditional on `MathCompCouplingGluing` and unrestricted
`relational_lub`. Only the pre-authorized Gate M file uses relaxed checking;
its unsafe-hierarchy flag is recorded separately, with the safe generic
theorem checked as an untainted control in that session. This does not prove
normally checked direct MathComp assembly or eliminate either premise.

## Preservation and remaining scope

`audit_direct_iteration.py` freezes all 413 prior Rocq modules byte-for-byte,
except four exact aggregate imports and one exact Gate M regression append.
The four new safe modules are the machine, generic law, thin completion
specialization and consumer regression. Old fold/protocol/theory proofs and
contract snapshots are unchanged; historical audit adapters reconstruct
their exact previous source view.

The underlying monomorphic syntax/interfaces have not been made universally
universe-polymorphic. This resolves the concrete uniformity/fold obstruction,
not every conceivable universe instantiation. Arbitrary-target Reader/Writer
commuting squares and all Conway/Elgot laws are still not claimed: inherited
uniformity alone is not those additional theorems.

## Local validation

Results are recorded after execution; remote CI is excluded by request.

- Full `opam exec -- dune build`, including safe AllImports and extraction.
- 347 Python tests passed.
- Architecture/source-soundness checks: 417 modules, 415 Gate S and the same
  two explicitly unchecked Gate M modules.
- 465 retained compiled contracts and 266 public owner/helper contracts
  unchanged; previous 19 eventful-iteration and 24 iteration-algebra safe
  contracts rechecked. The old protocol-only negative probe still fails
  specifically by universe inconsistency.
- 29 new safe compiled contracts checked jointly after AllImports; full
  uniformity and actual fold consumers are positive endpoints there.
- New Gate M full-uniformity endpoint and safe control checked separately;
  only the former has an unsafe-hierarchy declaration flag.
- Existing Gate M snapshot unchanged: 37 direct endpoints and six safe
  controls, with logical assumptions and unsafe-hierarchy reports checked.
- Joint `coqchk -norec` passed for all four new safe module bodies.
  Dependencies are trusted: this is not a recursive whole-library kernel
  audit, nor a claim of checked Gate M universes.
