# MathComp backend: native completeness and explicit trust boundary

## Names and entry points

The PTree assembly is `Eq/Backend/MathComp.v`; its program regressions are in
`tests/MathComp.v`. Import the assembly explicitly with
`From PTree.Eq.Backend Require Import MathComp.` Neither file belongs to the
safe aggregate. Both retain the existing, exact Gate M exception.

The assembly exposes `mathcomp_tree`, `mathcomp_head`, `mathcomp_frontier`,
`mathcomp_kernel`, `mathcomp_hitting`, `mathcomp_hitting_exists`,
`mathcomp_peutt`, `mathcomp_peutt_refl`, `mathcomp_bind_cofinal`, and
`mathcomp_peutt_bind`. The former `direct` qualifier has been removed from
these names, their module paths, and the audit tooling; no compatibility
aliases are retained. This is a naming change, not a change to mathematical
premises, canonical routing, or the universe trust boundary.

`mathcomp_direct_bernoulli` in the binary-oracle example is different: here
"direct" describes the one-draw specification program, contrasted with the
oracle algorithm, not a backend variant.

## Model and status

Backend pair: `MN = MF = MathCompKernelMeasure R`. There is no MathComp +
FreeOmega backend. Native order, omega/continuity and relational bind are
proved with normal universe checking. Recursive-frontier assembly remains
isolated in Gate M; coupling composition retains the explicit
`MathCompCouplingGluing R` premise.

[Generic bind](GENERIC_BIND.md) supplies the shared upper-layer proof.
Completed removal, naming and native-order stage reports remain in Git;
they are not current mathematical gaps. See [generic consumers](GENERIC_CONSUMERS.md)
for remaining model-specific premises, including unrestricted relational-lub.

## Capabilities

| Capability | Location / status |
| --- | --- |
| Returned-value order; source bind monotonicity | Checked `OrderLaws.v` |
| Increasing-chain lub existence; source bind continuity | Checked `OmegaLaws.v` |
| Continuation bind continuity, including AE hypotheses | Checked `OmegaLaws.v` |
| Mixed omega, diagonal, double-limit Fubini, omega AE | Checked `OmegaLaws.v` |
| Actual joint-kernel bind; BindLaws / MixedMeasureLaws | Checked `BindLaws.v` |
| Bind/order compatibility, directed cofinality, increasing-chain selector | Checked `BindOrder.v` |
| Coupling composition | Existing explicit `MathCompCouplingGluing R` premise |
| Every PTree has complete stable hitting | Gate M `mathcomp_hitting_exists` |
| Arbitrary eventful bind fuel cofinality | Gate M `mathcomp_bind_cofinal` |
| Unconditional eventful bind congruence | Gate M `mathcomp_peutt_bind` |
| Unbounded retry, bind, Vis, nested retry / diagonal limit | Gate M `MathComp.v` regressions |

“Unconditional” bind means no supplied scheduling/cofinality premise; the
existing explicit gluing premise of the behavioral core remains. No new
probability axiom or representation has been introduced. The generic extraction
adds only probability-level law/selection capabilities, proved by both backends.

## Checked mathematics (Gate S)

Native order compares returned-value events, not arbitrary root events containing
`MCBottom`: cemetery mass may decrease as returned mass increases. `OrderLaws.v`
proves source-bind monotonicity via nonnegative integrands that vanish at bottom,
first for simple functions and then by their supremum. This avoids incorrectly
using a global order on the completed probability measures.

`OmegaLaws.v` constructs an actual MathComp subprobability for each increasing
native chain. On a set `U` it takes `sup_n mu_n(U ∩ returned)`. The construction
proves finite additivity, countable subadditivity and mass at most one, then
builds the standard MathComp measure. It does not take a supremum of cemetery
mass, which need not increase, and does not assume lub existence.

Source continuity first proves convergence of integrals of nonnegative simple
functions zero at bottom, then uses the supremum over simple minorants.
Continuation continuity uses MathComp monotone convergence. For the AE version,
bad branches are replaced by zero and the result is transported back through
AE equality. Diagonal continuity is derived from these two continuities and
the double-limit theorem: `(i,j) <= (max i j,max i j)` makes the diagonal cofinal.
Omega AE follows from zero measures of complement events.

`BindLaws.v` chooses an existing continuation joint on each related input pair,
using classical choice. Off-support choices are irrelevant by AE support.
All sets of the joint carrier are measurable, so the selected family is a
measurable subprobability kernel. Integrating it against the input joint gives
an actual output joint. Projection integrals prove both returned marginals;
integration of the null complement proves relational support. Neither this
construction nor any new native omega theorem assumes gluing.

`Retry.v` independently proves that, for `0 < q <= 1`, the equation
`mu ≡ bind (Bernoulli q) (fun b => if b then target else mu)` forces `mu ≡ target`.
All root masses are finite (at most one), so ordinary real cancellation is
valid. This is a checked mathematical result, not an unchecked PTree argument.

## Program tests (Gate M)

`Examples/MathCompPrograms.v` defines guarded retry and nested-retry syntax
with normal checking; it does not instantiate a recursive measure of heads.
Its client `tests/MathComp.v` performs that instantiation:

- `retry_hitting`: any positive success probability yields the Dirac
  returned head; existence comes from the proved native omega laws.
- `unbounded_retry`: retry is `peutt` to immediate return.
- `eventful_bind_rewrite`: retry followed by an arbitrary eventful
  continuation rewrites to that continuation.
- `nested_unbounded_retry`: two sequential unbounded retries return
  the chosen value, with independently chosen positive success probabilities.
- `nested_retry_diagonal`: split source/continuation approximants
  converge along their common diagonal to the same returned head. This consumes
  the proved diagonal law, not finite stabilization of the inner loop.
  Diagonal and Fubini both derive from `mathcomp_native_double_diagonal`,
  the same diagonal cofinality theorem; neither instance requires the other
  instance as a typeclass premise.
- `retry_vis_interaction` and `retry_before_vis`: visible
  interaction and weak Tau rewriting.

`Eq/BindScheduling.v` proves the PTree-specific fuel bridge: global fuel `n` is bounded
by diagonal fuel `n`, while split fuel `(n,m)` is bounded by global fuel `n+m`.
`BindOrder.v` discharges its probability obligations using checked native
algebra and setwise supremum cofinality, and supplies the increasing-chain lub
selector. `Eq/Backend/MathComp.v` now merely instantiates this generic bridge and applies
`Eq/Bind.peutt_bind`, including heterogeneous final carriers and relations.
The previous native-specific finite inductions, `cid` frontier selector and
postfixed coinduction have been removed. Generic bind now uses the supplied
selector instead of `ClassicalChoice.choice`; no extra logical axiom or
FreeOmega instantiation is needed. `heterogeneous_bind` tests this route.

The old negative hitting-existence probe had an extra explicit interface
argument. It is now a genuinely typechecked positive application with the
correct signature, rather than evidence of a missing capability.
The isolated `MathCompOrder.v` still tests that importing only order does not
load the later omega module.

## Exact trust split

Only these two exact files may contain one `Local Unset Universe Checking.`:

- `Eq/Backend/MathComp.v`
- `tests/MathComp.v`

The allowlist is unchanged. No native mathematics, safe example, Domain,
generic theory or public facade may use the bypass or depend transitively on
Gate M. Safe AllImports contains every Gate S module and excludes both Gate M
files. Full `dune build` builds both groups, so it must **not** be called a
universe-checked whole-library build.

Gate M remains **not a universe-consistency result**. The dedicated audit
records Coq's per-declaration unsafe-hierarchy flags and session-level
`Type hierarchy is collapsed (logic is inconsistent)` report separately
from logical axioms. Safe controls must have no unsafe declaration flags,
even when queried in that session. No safe audit uses the bypass.
The original checked negative universe probes remain intact.

## Local verification

```sh
opam exec -- dune build
python3 tools/audit_mathcomp.py --gate S --build
python3 tools/audit_assumptions.py --check
python3 tools/audit_soundness.py --check
python3 tools/audit_api.py --check --surface-only
python3 tools/audit_architecture.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
python3 tools/audit_mathcomp.py --gate M
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Prob.Backend.MathComp.OmegaLaws \
  -norec PTree.Prob.Backend.MathComp.BindLaws \
  -norec PTree.Prob.Backend.MathComp.Retry \
  -norec PTree.Examples.Probability.MathCompOmega \
  -norec PTree.Examples.MathCompPrograms \
  -norec PTree.Tests.AllImports
```

Use [Maintained verification](AUDITING.md) for current snapshot groups and
source-safety checks. Gate M snapshots record unsafe flags separately and
are not evidence of universe consistency. The targeted safe `coqchk -norec`
command above trusts dependencies and is not a recursive whole-library audit.
Repeat `-norec` for each target: it is a per-module option, not a global switch.
Historical build/test counts remain in Git; no remote CI result is implied.
