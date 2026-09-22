# Joint universe consistency

## Root cause and repair

The aggregate failure was a real incompatibility between compiled clients,
not merely a `coqchk` invocation problem. At the layout snapshot, each of
these two-module imports reproduced it in ordinary `coqtop`:

The example import below is displayed in the current `Examples` namespace;
at that historical snapshot its prefix was `PTree.CaseStudies`.

```coq
From PTree.Examples.BernoulliFactory Require Import BernoulliFactoryComposition.
From PTree.Regression.Semantics Require Import CanonicalPartialDivergence.
```

Replacing the second import by
`PTree.Regression.Backend.UnifiedFrontierEnum` reproduced another instance.
Coq reported a strict inequality between shared PTree sampling universes
that the other client had already equated (for example,
`PTreeDefinition.61 < PTreeDefinition.51` versus their equality).

Both old regressions instantiated native samples and behavior with the same
monomorphic Enum interface. Heads contain recursive trees, and therefore
live above the sampled carrier universe. Those regressions could compile
alone by constraining the shared universe levels, but the constraints were
incompatible with clients using the general native-sampling universe.

The repair migrates those two clients to the maintained two-level pair:

```text
native samples:       Enum
complete head measures: FreeOmega Enum
```

No constructor, `peutt` generator, MDP/transition definition, measure axiom,
or global universe declaration is changed. Raw Enum numerical calculations
remain legitimate on low-universe observations. They are not used as the
high-universe carrier of complete recursive heads.
The partial-divergence regression also locally disables minimization to Set:
its unconstrained `FOZero` query must remain in that behavior universe.

## Preserved regression content

- `UnifiedFrontierEnum` still proves the sampled program's frontier
  certificate and equality of split-mass representations. Its equality is
  now the observable FreeOmega quotient, derived from native Enum coupling.
- `CanonicalPartialDivergence` keeps the original Enum programs. Finite
  spin approximants are now proved exactly `FOZero`, strengthening the old
  indicator-expectation calculation. Complete hitting and the nonempty
  interaction query are zero; an explicit native observation has mass zero.
- A zero-mass query remains distinct from the total `false` rejection.
- The half-return/half-divergence program still cannot be `peutt` to a
  total return. Its head witness is a fair sample with one `FORet` branch
  and one `FOZero` branch. The existing proved quotient scalar model
  preserves mass and separates 1/2 from 1; no normalization is performed.

The two finite-approximant lemmas are renamed from `..._expect_zero` to
`..._zero` to reflect the stronger statement. The remaining regression
endpoints retain their names but refer to the correct behavior carrier.
This is a backend repair, not a namespace-only change.

## Logical dependencies

The two frontier endpoints audit as closed under the global context.
The complete zero-hitting proof inherits `eq_rect_eq` through the existing
FreeOmega laws. The partial-divergence separation now uses the already
proved extended-real quotient-mass model instantiated with the standard
real construction, so its assumption audit includes the existing choice,
functional/propositional extensionality, dependent equality, and
`ClassicalDedekindReals.sig_not_dec` / `sig_forall_dec` dependencies.
This is a larger inherited dependency footprint than the old direct Enum
calculation, not a new axiom or a new premise asserting the desired result.

## Permanent prevention

`Regression/Infrastructure/AllImports.v` requires every other Gate S (normally checked)
Coq module in one universe context. Dune compiles it as part of the normal
build. `tools/audit_architecture.py --aggregate-only` fails if that inventory omits a new module,
contains extras, duplicates or is unsorted; CI runs this inventory check
before building. `Require` rather than `Require Import` avoids exporting
all short names while still merging the universe constraints.
The two explicitly universe-unchecked MathComp direct modules are excluded
from this safe aggregate and checked in a separate Gate M session; see
[the direct-backend trust boundary](MATHCOMP_DIRECT.md). This does not repair
their universe inconsistency or weaken Gate S's checked negative probes.
After building, CI also rechecks the two repaired regressions and
`PEuttAlgebra` together with `AllImports` in a single `coqchk` process.

The historical whole-library proof audit was interrupted after roughly
40 minutes and is not claimed to pass. The maintained targeted check is
documented in [architecture](ARCHITECTURE.md) and
[Cleanup B validation](CLEANUP_B_VALIDATION.md):

```sh
python3 tools/audit_architecture.py --aggregate-only
opam exec -- dune build
python3 tools/audit_api.py --surface-only --kernel
```

It checks selected module bodies together using `-norec`; dependencies load
into the same universe context but their proofs are not recursively rechecked.
This does not replace the separate final Gate D whole-library audit.

The checker uses its default ordinary conversion, which can be slow on
`native_compute`/`vm_compute` casts. A separate diagnostic run enabling
`-bytecode-compiler yes` hit a Coq 8.20.1 internal assertion in
`kernel/vmbytegen.ml:942`; that run is **not** counted as passing. The
maintained command does not enable this optimization or disable any universe
checks.

No module is excluded from that check. The dependency report excludes only
the import-only harness from *substantive client counts*, after checking its
coverage; otherwise that test would misleadingly make every leaf look used.

The historical layout proof-text audit remains frozen to
`92e0841 -> 6194bdf`. It does not claim that this subsequent repair is
proof-text identical to the old one-level regressions.
