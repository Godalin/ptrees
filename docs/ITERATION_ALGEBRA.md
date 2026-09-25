# PTree behavioral monad laws and carrier-indexed iteration algebra

Baseline: `d864423b`. This is an additive consumer layer over the existing
generic bind, structural bridge and eventful iteration proofs. It is **not**
a completed arbitrary-target fold/Elgot interface.

## Completed endpoints

Opt in explicitly:

```coq
From PTree.Interp Require Import IterationAlgebra.
(* Or, for the existing canonical completion profile: *)
From PTree.Interp.FreeOmega Require Import IterationAlgebra.
```

No global Eq1, law instance, hint, routing change or public re-export is added.

- `ptree_peutt_eq1`: the explicitly selected raw peutt equality as ITree's Eq1.
- `ptree_peutt_equivalence`: equivalence of that equality.
- `ptree_peutt_monad_laws`: the existing ret/bind operations satisfy
  ITree's MonadLawsE, including Proper_bind.
- `peutt_iter_uniform`: pure-map uniformity for specified state/result carriers.
- `ptree_peutt_iter_unfold`: the behavioral fixed-point equation, with the
  administrative retry Tau removed.
- `ptree_peutt_iter_tau_step`: inserting Tau before every step preserves peutt.
- `ptree_peutt_iter_finite_stutter`: every state may choose its own finite
  number of inserted Taus. There is no uniform numerical bound on these
  delays across an infinite execution.

The completion module supplies the existing certificates, without copying
the proofs. Its Eq1 unfolds to the canonical observable relation, not the
auxiliary structural FreeOmega interpretation.

The monad package is exercised by actual rewriting with the existing
`MonadLawsE.bind_ret_r`, and by the existing ReaderT, ExceptT and WriterT
law constructors. Writer still needs ordinary MonoidLaws, not commutativity.
No generic transformer theorem was changed.

## Uniformity proof

For `h : I -> J`, the square is

```text
bind (f i) (Ret ∘ iteration_map h) ≈ g (h i)
------------------------------------------------
iter f i ≈ iter g (h i)
```

`pstruct_return_map` first relates a tree to its mapped returns under any
relation containing the graph of the map. Structural-to-behavioral inclusion
and right endpoint transport turn the square into a step relation under
`sum_rel (fun i j => h i = j) eq`. The existing heterogeneous eventful
congruence then proves the conclusion.

No injectivity or inverse of h is needed. The regression collapses an
unbounded natural-number counter to unit while retaining repeated visible
queries. The theorem also permits silent divergence and nonreturning steps
inherited from the existing congruence.

Finite stuttering uses that same congruence and ordinary finite Tau
transparency. It is **PTree-specific**: it is not a new stuttering axiom for
arbitrary MonadIter targets, nor a theorem about every possible inserted
effect or arbitrary rescheduling.

## Important open boundary: full iteration_uniform packaging

The existing `Core/IterationLaws.iteration_uniform` quantifies over the
entire input universe of the upstream, monomorphic Eq1 interface. A theorem
for separately instantiated carriers is not automatically a value of this
stronger interface.

The current eventful iteration proof constructs an auxiliary event with
response type `I+A`. Consequently its universe constraints put the loop
state/result types in the PTree event-response universe. In the actual
joint client context, lifting this proof to the entire Eq1 domain is rejected
by the universe checker. PTree fold also uses a whole source tree as an
iteration state, so silently substituting the small-state theorem in its
law premise is not justified.

This was discovered by trying the real State/Exception fold consumers,
not by the standalone compilation of the law module. An initial standalone
full-package proof compiled, but its constant could not be instantiated in
that client context. It is **not retained** as a misleading public endpoint.

The positive `high_uniformity` regression uses carriers strictly above Set:
the result is not merely Set-only. It nevertheless does not establish
unrestricted Eq1-wide uniformity. A separate negative probe preserves that
distinction; the Python audit also reruns the attempted definition and
requires the actual error to be **universe inconsistency**, not a missing
name, wrong arity or missing instance.

This is a limitation of the current proof/interface combination, **not**
a mathematical counterexample to PTree uniformity, and not a proof that no
other checked proof can fill the interface. The natural next investigation
is a direct iteration machine/adequacy argument that does not place the
iteration state in an auxiliary Vis response. A redesign of the syntax,
upstream interfaces, or additional checker relaxation has not been attempted.

Therefore:

| Claim | Status |
| --- | --- |
| Explicit PTree Eq1 / equivalence / MonadLawsE | proved and consumed |
| Specified-carrier pure-map uniformity | proved |
| PTree fixed point and state-dependent finite Tau stuttering | proved |
| Full Eq1-wide iteration_uniform from this protocol proof | rejected; checked boundary |
| State/Exception generic fold square instantiated with this PTree target | not established |
| Arbitrary-target Reader/Writer commuting | remains open |
| All Conway/Elgot iteration laws | not claimed |

The old State/Exception conditional fold theorems and concrete ITree-target
Reader/Writer squares remain unchanged and valid.

## Requirements and assumptions

MonadLawsE consumes existing generic algebra/bind theorems and the explicit
`relational_mixed_bind / relational_zero / relational_lub` certificates,
with relational bind derived from existing BindLaws. The compiler drops
unused Section capabilities; the complete endpoint signatures are frozen
in `ITERATION_ALGEBRA_CONTRACTS.json`.

Uniformity and finite stuttering inherit the sufficient eventful-iteration
probability profile: native Core, frontier Core/Bind/order/omega/cofinality,
diagonal/Fubini, bind-order and mixed-bind-order, directed cofinality,
omega selection, and the relational certificates. No theorem-level
capability or new probability axiom is introduced.

The generic MonadLawsE proof is closed under its explicit context.
Generic equivalence and iteration endpoints inherit only the existing
`Eqdep.Eq_rect_eq.eq_rect_eq`; no excluded-middle dependency is added.
FreeOmega specialization additionally inherits existing functional
extensionality; finite-real clients retain their native classical foundation.
The logical-axiom whitelist is unchanged.

The same generic proofs are instantiated in the existing MathCompDirect
regression only. Gluing and relational-lub closure remain explicit premises.
Its unsafe-hierarchy/session flags are recorded separately with an untainted
generic control. This says nothing new about normally checked MathComp
assembly; Gate M does not expand.

## Conservation and verification

The additive audit freezes all 410 prior theory files, permitting only three
new safe modules, their sorted AllImports entries, and an exact append to
the already-authorized MathComp regression. Core syntax, interfaces,
canonical routing, FreeOmega, handler machines and all old proof bodies are
unchanged. Old compiled snapshots are not regenerated.

New compiled contracts are checked **after importing safe AllImports**,
rather than in an isolated context that could miss this kind of universe
constraint. The negative full-interface probe is checked there too.
Local validation results are recorded below; CI is excluded by request.

## Local validation completed

- Full `opam exec -- dune build`, including safe AllImports and extraction
  targets; existing extraction warnings are unchanged.
- 337 Python tests, including ten new scope/consumer/boundary tests.
- Architecture and source-soundness audits: 413 modules, 411 Gate S and
  the same two Gate M modules.
- 465 retained compiled contracts and 266 public owner/helper contracts
  unchanged; the previous 19 eventful-iteration contracts also rechecked.
- 24 new safe type/assumption contracts queried in the joint AllImports
  context; two new Gate M endpoints and one safe control checked separately.
- Existing Gate M snapshot unchanged: 37 direct endpoints and six safe
  controls, with unsafe-hierarchy flags recorded rather than hidden.
- Full-interface rejection confirmed specifically as a universe error.
- Joint `coqchk -norec` on the three new safe module bodies. Dependencies
  are trusted; this is not a recursive whole-library or Gate M kernel audit.
- `git diff --check`.

No remote CI was consulted or counted as evidence. The failed initial
full-interface experiment is reported above and is not counted as a proved
law package or a completed PTree-target fold theorem.
