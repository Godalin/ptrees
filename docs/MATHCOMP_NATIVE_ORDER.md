# MathComp native order: checked mathematical increment

Baseline: `c9a1a6f`. This completes the native `SemanticMeasureOrderLaws`
package, not the full direct MathComp backend or the entire native omega phase.
All new mathematics is in Gate S with normal universe checking.

## Mathematical route

`mathcomp_node_le mu nu` compares measures of returned-value events. It does
not compare sets containing `MCBottom`: unfinished/cemetery mass can decrease
when returned mass increases. Consequently applying a global measure-order
integral theorem directly to the original roots would be incorrect.

`OrderLaws.v` instead proves:

1. `mathcomp_native_sintegral_le`: comparison of nonnegative simple-function
   integrals when the simple function is zero at bottom. Its zero-valued fiber
   contributes zero; every nonzero fiber excludes bottom, so native order applies.
2. `mathcomp_native_integral_le`: comparison for any nonnegative extended-real
   integrand zero at bottom, by the definition as a supremum of simple minorants.
   Every such minorant is also zero at bottom. No measurability premise is
   needed for this inequality between MathComp's nonnegative lower integrals.
3. `mathcomp_native_bind_le_mu`: the root-bind integral has precisely such an
   integrand on a returned target event. Extending the continuation at bottom
   produces a Dirac bottom measure, which assigns zero to that event.
4. `MathCompNativeOrderLaws`: combines the new source monotonicity with the
   existing reflexivity, transitivity, least-zero and continuation monotonicity.

No gluing, relational bind, omega existence or order capability is assumed in
these proofs. No class, probability representation or axiom is introduced.

Three auxiliary results prepare the next phase: order antisymmetry yields
`mathcomp_kernel_eq`, and any supplied `mathcomp_kernel_lub` witness is an
upper bound and a least upper bound. These are NOT lub-existence results.

## Checked regressions

`Regression/Backend/MathCompOrder.v` imports only the native/interface layer.
It checks that FreeOmega, peutt and the direct assembly have not been loaded.
It instantiates order without a `MathCompCouplingGluing` context and retains
a negative native omega inference probe.

The tests establish:

- native zero is below return, even though their cemetery masses are 1 and 0;
- sampling Bernoulli(q) and discarding its false branch has returned mass
  exactly q, for 0 <= q <= 1;
- this possibly partial sample is below the version keeping both branches,
  and the inequality survives a further arbitrary kernel bind;
- generic `sem_bind_le_mu` resolves via the new native instance;
- any supplied lub lies below every upper bound of its chain.

The existing Gate M regression only gains the checked OrderLaws import and
changes its order probe from negative to positive. `Direct.v`, the exact
universe bypass policy, all existing Gate M endpoint signatures and their
unsafe reports are unchanged. General hitting existence and omega stay
negative; no recursive-frontier theorem is newly claimed here.

## Remaining mathematics

`SemanticOmegaLaws` still requires increasing-chain lub existence and bind
continuity, in addition to existing uniqueness/properness. Prove these in
Gate S next; do not supply an axiom or turn off universe checking to obtain
them. Only after that package is available can the direct hitting-existence
probe become positive. Bernoulli/bind/unbounded-program semantic cross-checks
remain subsequent direct-backend acceptance work.

## Verification

- Local full build: 271 modules, 269 Gate S and the unchanged two-file Gate M
  allowlist. No CI query or environment change.
- All 68 tool tests, architecture/API/source contracts: passed.
- All 505 frozen compiled signatures and assumptions: unchanged.
- Soundness audit: 199 frozen endpoints, 36 generic validation, 18 finite-real
  realization and 36 native MathComp endpoints passed. The last group now
  includes all seven new native order endpoints and seven safe regression
  definitions/results. No logical-axiom whitelist change.
- Joint targeted `coqchk -norec` of OrderLaws, MathCompOrder and safe AllImports:
  passed. Dependencies are trusted compiled objects; this is not recursive
  whole-library Gate D and does not check Gate M as safe theory.
- Explicit Gate S build and Gate M compiled audit both passed; the existing
  14 direct endpoint snapshots and two native controls are unchanged.
- Existing Core/Eq/Semantics/Interp and native mathematical source files are
  untouched. Two new Gate S files are added; existing `.v` edits only update
  the aggregate and the native-order inference probe in the direct regression.

This is native-order completion only. Omega completeness and general
direct-backend adequacy remain open.
