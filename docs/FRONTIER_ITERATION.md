# Generic complete-frontier iteration

Baseline: `5431810`. The native-round and staged absorbing-exit profiles
remain available. This increment removes both restrictions from the new
adequacy bridge: **complete steps may be MF-valued, and MF is arbitrary**.

## Public interface

`Interp/FrontierIteration.v` takes an actual step and its complete frontiers:

```coq
step  : I -> ptree E MN (I + A)
front : I -> MF (stable_head E MN (I + A))
Hfront : forall i, ptree_stable_hitting (observe (step i)) (front i)
```

`iteration_summary_target` resolves one complete head:

| Complete head | Action |
| --- | --- |
| `FHRet (inl j)` | retry at state `j` |
| `FHRet (inr a)` | absorb at `FHRet a` |
| `FHVis e k` | absorb at `FHVis e (fun x => bind (k x) iter_finish)` |

The visible continuation retains the actual iteration, including its retry
Tau. Forming a frontier neither consumes an event response nor chooses one
head from a mixture. `iteration_summary_kernel` binds the entire front into
these targets, preserving original weights and missing mass.

`iteration_summary_round` uses the existing absorbing-kernel approximants.
Round zero already retains stable Ret/Vis exits, while unresolved retries
contribute zero. This convention differs from the older native-round
helper whose zeroth approximant is entirely zero.
`iteration_summary_round_unfold` exposes the recurrence under `sem_eq`.

The main endpoints are:

```text
iteration_summary_hitting:
  all complete step certificates
  + lub of complete-round approximants = out
  -> stable_hitting (iter step i) out

iteration_summary_exists:
  all complete step certificates
  -> exists out, summary i out /\ stable_hitting (iter step i) out

iteration_summary_hitting_eq:
  summary i out + stable_hitting (iter step i) actual
  -> sem_eq actual out
```

No client cofinality proof, finite stopping bound, `no_event`, AST/totality,
finite state space, or native representation of the limit is required. The
client may leave the complete measure abstract and analyze only the desired
observations. The bridge does not itself calculate probabilities or prove AST.

## Reused proof, not a new capability

The existing generic `IterationMachine` already proves the hard finite-fuel
scheduling facts. The new bridge reindexes that machine by loop-entry states
instead of residual trees and proves the finite grids order-equivalent.
It then applies existing continuity:

```text
finite inner fuel × finite outer rounds
               |
         diagonal bind law
               v
complete MF step × finite outer rounds
               |
             Fubini
               v
complete-round lub = actual primitive-hitting lub
```

The final conversion reuses `iter_phase_diagonal_tree`; it does not assume
the very iteration adequacy it is supposed to establish. The generic main
theorem uses only existing Order, BindOrder, MixedBindOrder, Omega,
Cofinality, DirectedCofinality, Diagonal and Fubini laws. In particular it
does not require Core/coupling laws, relational-lub closure, OmegaSelection,
or a probability interface on MN itself. The optional round-unfold equation
uses Core and Bind laws, separately from adequacy.

Order equivalence is used for the finite scheduling grid; observable
`sem_eq` is used for the public unfolding and witness uniqueness results.
Neither is silently converted to the other for arbitrary frontier measures.

## Instances and boundary tests

- `Interp/FreeOmega/AbsorbingIteration.complete_iteration_hitting` applies
  the generic theorem, with `FOLub` of complete rounds as the explicit
  frontier. It is native-parametric, not SubEnumQ-specific.
- `Regression/Semantics/FrontierIteration` constructs a coinductive step
  that may search through arbitrarily many natural indices before exposing
  retry, completion or Vis. Its supplied step frontier is itself a `FOLub`
  of primitive approximants, not a native return distribution. The coin is
  an arbitrary SubEnumQ subdistribution; the zero coin is included.
  Additional checks preserve the recursive visible continuation and an
  offered event with an empty response type. Importing only the generic
  owner does not load FreeOmega or MathComp.
- `SubEnumRBehavior.real_complete_step_summary` consumes the same
  FreeOmega corollary with finite-real native sampling.
- `MathCompDirect.direct_complete_step_summary` instantiates the same
  generic theorem with `MN = MF = MathCompKernelMeasure R`. There is no
  MathCompCouplingGluing assumption. This client remains in the existing
  Gate M file; no new checker relaxation is introduced.

Exact hitting requires certificates for the **actual** step, including its
actual visible continuations. Replacing a step by a behaviorally equivalent
one does not make those continuations literally equal. The older staged
profile still uses whole-head behavioral lifting for that separate situation.

The existing VN/Adaptive quantitative observation proofs and all previous
theorem statements are preserved. RandomWalk migration, new probability
analysis, and a new proof of iteration congruence are not part of this change.

## Verification

Compiled signatures and logical assumptions are recorded in the existing
generic-algebra contract suite, with the MathComp client recorded separately
as Gate M. The five recorded generic endpoints are all `Closed under the
global context`. The FreeOmega corollary inherits only `eq_rect_eq`; it does
not inherit functional extensionality or choice. The MathComp client retains
the native model's existing classical/extensional assumptions and its
explicit unsafe-hierarchy flag. No new audit program or semantic axiom is
introduced.

Local validation:

- Full `opam exec -- dune build -j 2`, including AllImports and extraction.
- 141 tool tests; architecture, API surface and soundness source checks.
- 465 original main contracts and all 94 previous generic-algebra contracts
  unchanged. Nine new safe contracts bring that suite to 103; its three
  previous Gate M contracts are unchanged, with one new direct client.
- Joint `coqchk -norec` for FrontierIteration, the FreeOmega corollary module,
  the new regression and SubEnumRBehavior. This checks these safe module
  bodies while trusting dependencies, not the entire library recursively.
- The two-file Gate M allowlist is unchanged. The direct client is not
  included in the normally universe-checked kernel audit.
- CI was neither inspected nor used as an acceptance condition.
