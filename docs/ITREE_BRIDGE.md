# ITree probability effects to native PTree probability

Baseline: `002f0a6`. This increment is additive: it does not change the
PTree datatype, probability interfaces, canonical routing, handler calculus,
execution semantics, or MathComp trust boundary.

## The actual datatype bridge

`Core/ITreeBridge.v` defines:

```coq
probE MN X                  (* Sample : MN X -> probE MN X *)
from_itree : itree E A -> ptree E MN A
interp_itree : Handler MN E F -> itree E A -> ptree F MN A
elaborate : itree (probE MN +' E) A -> ptree E MN A
elaborate_closed : itree (probE MN) A -> ptree void1 MN A
```

`from_itree` is a guarded cofixpoint embedding Ret/Tau/Vis. It does not
interpret probability. `interp_itree h t` is then exactly
`PTree.interp h (from_itree t)`. The probability handler maps `Sample mu`
to `Prob mu Ret`; the sum handler forwards ordinary events with trigger.
No sampler, fuel, normalization, or external model is involved.

ITree can encode sampling as an external effect; PTree internalizes that
effect as a primitive probabilistic node. This is different from using
ITree's State/Reader signatures in an already-existing PTree, and from
`Execution/ITreeFold.v`, which goes in the opposite direction.

## Laws and their strength

`Interp/ITreeStructural.v` proves embedding bind/iter by direct structural
coinduction. General interpretation bind/iter then reuse the existing
PTree structural interpreter theorems. Postcomposition also reuses the
existing PTree interpreter composition proof.

`Interp/ITreeFacts.v` lifts these results through the generic
`pstruct -> peutt` theorem. The main endpoints are:

| Endpoint | Conclusion modulo `peutt eq` |
| --- | --- |
| `elab_ret` | interpreted Ret is Ret |
| `elab_tau` | source Tau is behaviorally transparent |
| `elab_event` | source Vis becomes handler followed by elaborated continuation |
| `elab_trigger` | a source trigger becomes its handler |
| `elab_sample` | Sample becomes native Prob |
| `elab_vis` | ordinary events remain Vis |
| `elab_bind` | interpretation preserves bind |
| `elab_iter` | interpretation commutes with guarded iteration |
| `elab_sample_trigger` | closed Sample trigger is `Prob mu Ret` |
| `elab_postcompose` | PTree post-interpretation equals interpretation with composed handlers |

The event equations are behavioral, not definitional: PTree interpretation
inserts an administrative Tau before the handler. The structural variants
explicitly retain it. The weak equations remove it by the existing Tau law.

The compiled generic signatures use existing native/frontier Core laws,
MixedMeasure operations, order/omega, and explicit relational mixed-bind,
zero, and increasing-lub certificates. Weak Tau elimination additionally
uses the existing frontier Bind and cofinality laws. No theorem-level
capability, existence axiom, global hint, or backend-specific proof is added.
Section assumptions unused by a particular theorem are absent from its
compiled signature; `ITREE_BRIDGE_CONTRACTS.json` records these precisely.

`Interp/FreeOmega/ITreeCompletion.v` merely discharges the existing
probability certificates. Its `free_omega_elab_*` names do not shadow the
generic owners. The bridge is an explicit opt-in import, not another
change to the default PTree facade:

```coq
From PTree.Core Require Import ITreeBridge.
From PTree.Interp.FreeOmega Require Import ITreeCompletion.
```

## Actual program

`Examples/ITreeSampling.v` defines a genuine source program:

```text
x <- ITree.trigger (Sample fair_coin);
y <- ITree.trigger (Sample fair_coin);
ITree.Ret (xorb x y)
```

`two_coins_elaborates` proves its elaboration equivalent to the native
PTree program with two `Prob fair_coin Ret` draws and the same xor result.
This is a reusable entry into the existing PTree algebra, not a replacement
implementation of that algebra. It does not separately prove that xor is
a single fair draw.

The same module contains a genuine ITree `iter` retry program and proves
its elaboration equivalent to PTree iteration of the elaborated step.
There is no fuel bound or claim that every execution terminates.

Regression checks also cover open sampling, ordinary event forwarding,
zero-mass native sampling without normalization, explicit administrative
Tau, handler postcomposition, and a carrier strictly above Set. Core-only
imports do not load probability semantics; no bridge client imports Gate M
or the independent OmegaVal validation layer.

## Precise boundaries

This is a homomorphism-like interpretation, not an isomorphism. A handler
need not be invertible. The established postcomposition theorem is:

```text
interp_PTree g (interp_itree h t)
    ≈ interp_itree (Handler.cat h g) t.
```

That original postcomposition theorem does not itself compare source
`ITree.interp` with target `PTree.interp`. The later
[source-preservation increment](ITREE_PRESERVATION.md) now proves both that
genuine source square and heterogeneous source `eutt -> peutt`, by separate
weak-simulation and scheduling arguments. The original structural proofs
remain unchanged and do not assume those later results.

The probability-free embedding additionally has the generic
`from_itree_eutt_iff`: on `from_itree` images, `eutt RR` and `peutt RR`
coincide under the existing Dirac/zero separation laws. FreeOmega discharges
these laws for both SubEnumQ and SubEnumR. This does not assert reflection
for an arbitrary handler or for sampling-event elaboration, nor does it
construct a subtype or inverse for all probability-free PTrees.

A commuting square for a source of type `itree (probE MN +' E) A`
must restrict the source transformation to preserve sampling. Arbitrary
source handlers may replace `Sample mu`; after elaboration an ordinary
PTree handler cannot do so, because it only handles Vis and preserves Prob.
ITree and PTree place their administrative Tau differently; the new square
explicitly proves this scheduling difference harmless, including for
internally returning and divergent handlers.

## Verification

The current `itree_bridge` contract group retains 61 compiled
definitions/theorems/examples and their logical assumptions. Check it with
`python3 tools/audit_contracts.py --group itree_bridge`; the probability-free
iff is additionally registered in `itree_preservation`. The root build checks
all bridge clients, while architecture and source-safety audits maintain the
generic/backend separation and the explicit Gate M boundary.

Historical additive-source audits and their module/test counts belong to the
original migration history, not the current checking workflow. Current
conservativity scope and verification are recorded in
[ITREE_PRESERVATION.md](ITREE_PRESERVATION.md). A targeted `coqchk -norec`
checks the selected safe module bodies while trusting dependencies; it is
neither a whole-library recursive audit nor an endorsement of Gate M.
