# MathComp: native mathematics, not a completion backend

Historical removal record: roles, counts and validation results below describe
that checkpoint, not the current backend. The [accepted direct MathComp
backend](MATHCOMP_DIRECT.md) at `5dac49a` supersedes the native-only future-work
decision, but preserves removal of MathComp + FreeOmega and all checked native
mathematics. Direct use remains isolated in Gate M, with explicit gluing.

Baseline: `965e7b1`. This is a removal/scope-consolidation stage, not new
probability theory. CI and environment changes are deliberately excluded.

## Maintained roles

| Model | Maintained role |
| --- | --- |
| SubEnumQ | Finite exact-rational native sampling, with `FreeOmega SubEnumQ` for complete PTree behavior |
| SubEnumR R | Finite-real native sampling, with `FreeOmega (SubEnumR R)` for complete PTree behavior |
| MathComp | Direct discrete kernel/measure and real-valued analytic results, including native joint witnesses; no recursive PTree frontier specialization |

Generic `MN`/`MF`, SemanticMeasure/SemanticOmega/MixedMeasure, PTree, stable
hitting, `peutt` and generic FreeOmega remain unchanged. Finite native models
are the maintained complete probability instances, not a new restriction on
generic theorems. The raw EnumQ compatibility development is also untouched.
MathComp Analysis continues to anchor the independent OmegaVal measure model;
removing the concrete MathComp-kernel completion does not remove that library
or its role in external validation.

## Removed, not replaced

- `MathCompBehaviorMeasure` and all completion imports supporting it in
  `Prob/Backend/MathComp/Measure.v`.
- `Regression/Backend/UnifiedMathCompFrontier.v`.
- `Examples/BernoulliFactory/UnifiedRealBernoulliMathCompCore.v` and
  `Examples/BernoulliFactory/OperationalRealBernoulliMathComp.v`.
- The example-only `MathCompOracleSupportLaws` class, whose sole frontend has
  been deleted; this is an approved removal from the source contract policy,
  not a relaxation of the logical-axiom whitelist.
- The MathComp completion section of `BackendCapabilities`, and the
  MathComp-specific completion cases of `MDPCoincidence` and
  `FiniteInternalNative`. Their generic and finite-backend tests remain.

The latter three sections were additional clients beyond the proposal's named
files; retaining them would leave the removed instantiation alive under local
aliases. No other FiniteInternal infrastructure was removed. All deleted
content is recoverable from git at the baseline above.

No new completion, wrapper, existential carrier, typeclass or universe escape
replaces the removed path.

## Native results retained

`MathComp/Kernel.v`, `MathComp/Coupling.v`, `MathComp/Domain.v` and
`Examples/BernoulliFactory/RealBernoulliMathComp.v` are byte-for-byte unchanged.
The native theorem section of `MathComp/Measure.v` is unchanged apart from
its scope comment. Ordinary bind, subprobability validity, foundational AE,
native lifting, `mathcomp_bernoulli`, and `mathcomp_coupling_realization` stay.
Coupling composition still has its existing explicit `MathCompCouplingGluing`
premise; no new instance or existence axiom was added.

`SelfModel.v` becomes `NativeLaws.v`. Its useful same-carrier kernel algebra
is retained: mixed unit/node-bind laws, total properness, order basics,
zero-prefix/constant-lub laws and continuation-side bind monotonicity.
Identifiers are mechanically renamed `MathCompSelf* -> MathCompNative*` and
`mathcomp_self_* -> mathcomp_native_*`, with no old-name aliases. Beyond the
role comment, proof text is unchanged under that explicit renaming and the
section name change. This is not a promised PTree self-model.

`Regression/Backend/MathCompSelfModel.v` moves to
`Regression/Infrastructure/MathCompUniverse.v`. It checks that importing the
native modules alone does not load the formal completion, then retains the
known joint-import context, positive tree/head controls and the checked
negative same-carrier frontier/kernel/peutt definitions. The sealed-carrier
universe obstruction remains a scope boundary. This stage neither repairs it
nor claims universe constraints are the only missing mathematical property.

## Permanent safeguards

- Native MathComp ownership rejects direct FreeOmega dependencies and a
  `MathComp/FreeOmega` namespace. Its full transitive dependency closure must
  also be completion-free.
- Source checks reject the deleted behavior alias and concrete completion
  instantiations, including the simple local aliases formerly used by tests.
  This lexical check is not a general Coq elaborator; import-closure checks
  provide an independent dependency guard.
- Generic arbitrary-native completion theorems remain allowed.
- The 505 compiled contracts remain frozen. The deleted class and tests are
  removed explicitly from the source policy; no remaining contract is silently
  regenerated.
- `audit_soundness.py --mathcomp-native-only` checks 22 retained native,
  analytic and infrastructure endpoints against the existing logical-axiom
  whitelist, and rejects completion/frontier types in those signatures.

## Local validation commands

```sh
opam exec -- dune build
python3 tools/audit_architecture.py --check
python3 tools/audit_api.py --check --surface-only
python3 tools/audit_soundness.py --check
python3 tools/audit_assumptions.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.Prob.Backend.MathComp.Measure \
  -norec PTree.Prob.Backend.MathComp.NativeLaws \
  -norec PTree.Prob.Backend.MathComp.Coupling \
  -norec PTree.Examples.BernoulliFactory.RealBernoulliMathComp \
  -norec PTree.Regression.Infrastructure.MathCompUniverse \
  -norec PTree.Regression.Backend.BackendCapabilities
```

The kernel command checks six module bodies jointly, trusting compiled
dependencies. It is a targeted check, not recursive whole-library Gate D.

## Verification result

- Full local build and sorted AllImports: passed, 267 modules (270 before
  removal; three deletions and two namespace relocations).
- Architecture inventory, source-safety and curated API checks: passed.
- All 59 tool tests: passed, including rejected direct/aliased completion
  instantiations and indirect native-to-completion imports.
- All 505 frozen compiled signatures/assumptions: unchanged.
- Full soundness audit: 199 frozen endpoints unchanged; 36 generic validation,
  18 finite-real realization and 22 retained MathComp native endpoints passed
  the existing logical-axiom whitelist.
- Targeted six-module joint kernel check above: passed.
- Source conservation against `965e7b1`: 168 protected generic/finite-backend
  and retained native/analytic files are byte-identical. The native Measure
  section is unchanged ignoring comments/whitespace; NativeLaws proof text is
  exact under the documented identifier and section renaming.
- No new axiom, class, probability representation, universe workaround or
  environment change. CI was not queried or modified.
