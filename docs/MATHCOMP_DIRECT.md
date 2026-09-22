# Direct MathComp: native completeness and explicit trust boundary

Direct pair: `MN = MF = MathCompKernelMeasure R`. There is no MathComp +
FreeOmega backend. The universe policy accepted at `c9a1a6f` is unchanged;
the native order baseline is `561dc9a`. This increment completes the requested
native omega/relational-bind mathematics and direct program acceptance.
Accepted theory-completion baseline: `5dac49a`. This round is closed;
coupling composition retains its explicit gluing premise and Gate M retains
its isolated universe relaxation.
No CI work or environment changes are included.

## Capabilities

| Capability | Location / status |
| --- | --- |
| Returned-value order; source bind monotonicity | Checked `OrderLaws.v` |
| Increasing-chain lub existence; source bind continuity | Checked `OmegaLaws.v` |
| Continuation bind continuity, including AE hypotheses | Checked `OmegaLaws.v` |
| Mixed omega, diagonal, double-limit Fubini, omega AE | Checked `OmegaLaws.v` |
| Actual joint-kernel bind; BindLaws / MixedMeasureLaws | Checked `BindLaws.v` |
| Coupling composition | Existing explicit `MathCompCouplingGluing R` premise |
| Every PTree has complete stable hitting | Gate M `mathcomp_direct_hitting_exists` |
| Arbitrary eventful bind fuel cofinality | Gate M `mathcomp_direct_bind_cofinal` |
| Unconditional eventful bind congruence | Gate M `mathcomp_direct_peutt_bind` |
| Unbounded retry, bind, Vis, nested retry / diagonal limit | Gate M `MathCompDirect.v` regressions |

“Unconditional” bind means no supplied scheduling/cofinality premise; the
existing explicit gluing premise of the behavioral core remains. No new
probability axiom, class or representation has been introduced.

## Checked mathematics (Gate S)

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

## Direct program tests (Gate M)

`Examples/MathCompPrograms.v` defines guarded retry and nested-retry syntax
with normal checking; it does not instantiate a recursive measure of heads.
Its client `Regression/Backend/MathCompDirect.v` performs that instantiation:

- `direct_retry_hitting`: any positive success probability yields the Dirac
  returned head; existence comes from the proved native omega laws.
- `direct_unbounded_retry`: retry is `peutt` to immediate return.
- `direct_eventful_bind_rewrite`: retry followed by an arbitrary eventful
  continuation rewrites to that continuation.
- `direct_nested_unbounded_retry`: two sequential unbounded retries return
  the chosen value, with independently chosen positive success probabilities.
- `direct_nested_retry_diagonal`: split source/continuation approximants
  converge along their common diagonal to the same returned head. This consumes
  the proved diagonal law, not finite stabilization of the inner loop.
  Diagonal and Fubini both derive from `mathcomp_native_double_diagonal`,
  the same diagonal cofinality theorem; neither instance requires the other
  instance as a typeclass premise.
- `direct_retry_vis_interaction` and `direct_retry_before_vis`: visible
  interaction and weak Tau rewriting.

`Direct.v` proves the PTree-specific fuel bridge: global fuel `n` is bounded
by diagonal fuel `n`, while split fuel `(n,m)` is bounded by global fuel `n+m`.
Native setwise supremum cofinality discharges the scheduling premise of
the generic bind-hitting theorem. Bind congruence reuses the generic
`bind_bisim_candidate` and specializes its postfixed proof: hitting witnesses
are selected using MathComp's existing `cid`. Directly calling the old generic
`peutt_bind` would inherit `ClassicalChoice.choice`'s additional logical axioms;
the specialization avoids that without modifying frozen generic theory or
expanding the existing logical-axiom whitelist. No FreeOmega instantiation is
used.

The old negative hitting-existence probe had an extra explicit interface
argument. It is now a genuinely typechecked positive application with the
correct signature, rather than evidence of a missing capability.
The isolated `MathCompOrder.v` still tests that importing only order does not
load the later omega module.

## Exact trust split

Only these two exact files may contain one `Local Unset Universe Checking.`:

- `Eq/Backend/MathComp/Direct.v`
- `Regression/Backend/MathCompDirect.v`

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
python3 tools/audit_mathcomp_direct.py --gate S --build
python3 tools/audit_assumptions.py --check
python3 tools/audit_soundness.py --check
python3 tools/audit_api.py --check --surface-only
python3 tools/audit_architecture.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
python3 tools/audit_mathcomp_direct.py --gate M
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Prob.Backend.MathComp.OmegaLaws \
  -norec PTree.Prob.Backend.MathComp.BindLaws \
  -norec PTree.Prob.Backend.MathComp.Retry \
  -norec PTree.Regression.Backend.MathCompOmega \
  -norec PTree.Examples.MathCompPrograms \
  -norec PTree.Regression.Infrastructure.AllImports
```

The frozen 505 safe compiled contracts and logical-axiom whitelist are not
regenerated. New native endpoints are checked independently for absence of
gluing or circular semantic-law premises. Gate M's expanded snapshot is
separate. Targeted safe `coqchk -norec` is not a whole-library recursive Gate D
audit and makes no normal kernel-consistency claim about Gate M.

`-norec` is repeated for every target: it is a per-module option, not a
global switch. An initial command with only one `-norec` accidentally started
a larger recursive dependency check; that run was stopped and is not counted
as passing validation.

Completed locally for this increment:

- Full `dune build`: 276 modules (274 Gate S, 2 Gate M); safe-only build also passed.
- AllImports, architecture and curated API checks passed.
- All 505 frozen compiled contracts and their assumptions unchanged.
- Soundness audit: 199 frozen contracts unchanged, plus 36 generic, 18
  finite-real and 80 native MathComp endpoints passed the existing axiom whitelist.
- All 69 Python tool tests passed.
- Gate M: 30 direct endpoints and 6 safe controls passed; every previously
  recorded endpoint retained its exact type, assumptions and unsafe flags.
- The six-module joint targeted kernel check shown above completed successfully.
- No CI run was checked or claimed successful; no environment was changed.
