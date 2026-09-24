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

A commuting square for a source of type `itree (probE MN +' E) A`
must restrict the source transformation to preserve sampling. Arbitrary
source handlers may replace `Sample mu`; after elaboration an ordinary
PTree handler cannot do so, because it only handles Vis and preserves Prob.
ITree and PTree place their administrative Tau differently; the new square
explicitly proves this scheduling difference harmless, including for
internally returning and divergent handlers.

## Verification

`audit_itree_bridge.py` freezes all 376 pre-existing theory files byte for
byte, except insertion of the six new sorted AllImports entries. It checks
the actual source datatype/native Prob definitions, generic ownership,
thin specializations, and absence of new assumptions or global search.
The previous handler audit consumes this additive-stage adapter without
weakening its own frozen baseline.

The new compiled snapshot covers 61 definitions/theorems/examples and
checks the existing logical-axiom whitelist. Existing snapshot files are
not regenerated.

Local verification completed:

- Full `opam exec -- dune build`, including safe AllImports and the existing
  extraction targets.
- All 284 Python tool tests; architecture and public-surface audits.
- 465 old compiled contracts unchanged; the original 60 handler-calculus,
  27 machine and 11 fusion/guarded contracts also unchanged.
- All 61 new compiled bridge contracts and assumptions checked.
- Soundness source audit: 382 modules, 380 Gate S and the same two Gate M.
- Joint `coqchk -norec` of the six new safe module bodies.
- `git diff --check`.

The kernel check trusts compiled dependencies; it is not a whole-library
recursive kernel audit. It does not check or endorse Gate M. No CI was
queried or counted. The full build retained the pre-existing extraction
opacity/output-directory warnings; kernel checking reported its normal
native-to-VM conversion fallback.
