# Generic bind extraction

Baseline: `6e35c19` (accepted definition-owned public modules).

## Result and boundary

`Eq/Bind.peutt_bind` is the single public heterogeneous bind congruence.
It is generic in `MN`, `MF`, the frontier operations and both return relations:

```text
peutt RR t u
(forall x y, RR x y -> peutt RS (k x) (h y))
------------------------------------------------
peutt RS (bind t k) (bind u h)
```

There is no `PEuttBindLaws` class, new probability axiom, alternative equality,
or change to `free_omega_approx`, `free_omega_qlift` or canonical routing.
The MathComp universe boundary is unchanged: native mathematics is checked;
only the two existing Gate M files perform unchecked recursive assembly.

## Why not sem_eq -> sem_le?

The observable FreeOmega model has quotient equality but structural order.
The new `Regression/Semantics/GenericBind.v` proves:

```text
FORet tt  qlift(eq)  FOLub (fun _ => FORet tt)
neither direction is structural approximation

FOSample mu (fun _ => FOZero)  qlift(eq)  FOZero
the sampled zero is NOT structurally below FOZero
```

In particular, a general `sem_eq_le` capability is refuted. Finite scheduling
does not normalize a zero-fuel `Prob` to bare bottom: it keeps its mixed node.
There is no change to the existing external-domain soundness interpretation.

## Explicit prototype, then small capabilities

`Eq/BindScheduling.v` retains the proved prototype with five explicit
hypotheses, rather than hiding its requirements in a PTree law package:

1. bind-left-unit holds in both directions of the approximation preorder;
2. `bind zero k <= zero`;
3. mixed associativity holds in both directions of the preorder;
4. mixed bind is monotone in its continuation;
5. mutually cofinal increasing chains have identical lub witnesses.

Its local `equiv` abbreviation is only the conjunction of two inequalities.
It is not exported as another user-facing equivalence or notation.

The compiled proof splits into:

```text
finite approximation-compatible algebra + ordinary bind order
    -> H_n(bind t k) <= split_(n,n)(t,k)
    -> split_(n,m)(t,k) <= H_(n+m)(bind t k)

increasing-chain cofinality
    -> ptree_bind_cofinal_all

existing diagonal continuity and relational bind
    -> stable hitting respects bind
    -> heterogeneous peutt_bind
```

Neither the scheduling prototype nor generic bind requires
`SemanticOmegaFubiniLaws` or `MixedMeasureOmegaLaws`. Those remain separate
capabilities for their existing consumers.

Only after this prototype compiled were its requirements packaged:

| Owner | Capability | Fields |
| --- | --- | --- |
| `Prob/Interface/BindOrder` | `SemanticMeasureBindOrderLaws` | left unit, left bottom in the preorder |
| `Prob/Interface/BindOrder` | `MixedMeasureBindOrderLaws` | mixed associativity, continuation monotonicity |
| `Prob/Interface/Omega` | `SemanticOmegaDirectedCofinalityLaws` | mutual increasing-chain cofinality |
| `Prob/Interface/Omega` | `SemanticOmegaSelection` | a chosen lub of an increasing chain |

The existing omega classes and their fields are unchanged. Selection is
operation-bearing data, not a global choice instance or an existential
transport axiom:

```coq
forall A (chain : nat -> MF A),
  sem_increasing chain -> {out : MF A | sem_lub chain out}
```

## Backend reuse and public ownership

`Prob/FreeOmega/BindOrder.v` proves the finite obligations by the existing
definitions/structural approximation, uses the existing cofinal-lub theorem,
and selects `FOLub chain`.

`Prob/Backend/MathComp/BindOrder.v` proves the same obligations from checked
native algebra/order facts and selects the already constructed native lub.
It imports no PTree theory and disables no checker.

The large FreeOmega finite-fuel induction bodies are replaced by applications
of the generic scheduling theorems. Existing FreeOmega scheduling helpers
remain as clients for the maintained iter/nested-grid development; their
statements do not change. Its former `peutt_bind` corollary is removed, and
the module re-exports the actual generic owner, not a same-name alias.

MathComp's separate approximation unfold/split induction, `cid` front-choice
helper and bind-postfixed coinduction are removed. Direct bind is now a
one-line application of the generic theorem, with independent source/result
relations and different final carriers. Existing retry, Vis and nested-limit
regressions remain, with an additional heterogeneous direct regression.

`PTreeFacts` directly exports `Eq/Bind`. Raw `PEutt.peutt_bind_cofinal` remains
available for callers supplying an explicit scheduling theorem, but now also
takes the increasing-chain selector. No export-order theorem shadowing returns.

The SubEnumR regression's old ssreflect `exact: Bind.peutt_bind` was replaced
with an explicitly profiled generic application after it triggered prolonged
instance search. This is a client elaboration change, not a new global hint.
Ordinary public `eapply peutt_bind; eassumption` remains tested unchanged.

## Assumptions and verification

The generic scheduling endpoints, raw bind endpoint with selection, and
final generic `peutt_bind` report `Closed under the global context`.
Their mathematical capabilities are explicit parameters, not hidden axioms.

The bind-path front witness is constructed from `sem_lub_choose`.
Other unrelated uses of `ClassicalChoice` in `PEutt.v` are not rewritten or
claimed eliminated. FreeOmega and MathComp concrete assumptions are audited
separately; removal of choice from this path does not erase dependencies of
the underlying native models.

The regression specialization has exactly the previous FreeOmega bind type
up to local binder names and printer whitespace. Its old assumption report had
`ClassicalUniqueChoice.dependent_unique_choice` and
`RelationalChoice.relational_choice`; both disappear. It still uses the
existing functional extensionality and `eq_rect_eq` dependencies. This is not
a claim that the concrete FreeOmega proof is axiom-free.

`tools/audit_generic_bind.py` freezes unrelated old sources, protects the
relation definitions and registry, and accounts for all 465 baseline
contracts. `GENERIC_BIND_CONTRACT_CHANGES.json` records complete before/after
entries for every changed signature or assumption report. Only the generic
bind owner and selector-bearing raw bind helpers may change mathematical
signatures; per-endpoint logical-axiom growth is rejected.

The comparison records 16 changed entries: four intentional type changes
(the generic owner and three selector-bearing raw helpers), plus downstream
assumption reductions. No other baseline type changes. The 465-entry manifest
keeps the same API/soundness/capability membership modulo the bind-owner rename.
`GENERIC_BIND_MATHCOMP_CHANGES.json` independently records the three removed
finite-scheduling helpers, the weakened cofinality signature (no gluing premise),
the fully heterogeneous direct bind, the new direct regression and reduced
dependency reports. Remaining direct types are unchanged; existing unsafe
declaration sets only shrink and the two-file Gate M boundary stays fixed.

The old public-module gate remains frozen at its accepted checkpoint; its
mutation tests use that checkpoint rather than weakening its preservation
rules to permit this later theorem extraction.

Validation commands:

```sh
opam exec -- dune build
python3 tools/audit_generic_bind.py --compiled --kernel
python3 tools/audit_api.py --surface-only
python3 tools/audit_architecture.py --check
python3 tools/audit_soundness.py --check
python3 tools/audit_mathcomp_direct.py --gate M
python3 -m unittest discover -s tools -p 'test_*.py'
```

The targeted joint kernel check covers 12 safe module bodies with `-norec`;
dependencies are trusted and Gate M is excluded. It is not a whole-library
recursive kernel check or a universe-safe claim about MathComp assembly.
CI is intentionally out of scope.

Completed local validation:

- Full build and AllImports: 311 modules, including 309 Gate S and 2 Gate M.
- All 145 Python tool tests passed; architecture and public-surface checks passed.
- All 465 compiled contracts match the reviewed migration manifest; 16
  before/after changes are recorded with no per-endpoint axiom growth.
- All 22 new generic/native/negative endpoints passed; the five audited generic
  scheduling/bind endpoints are closed under the global context.
- Existing soundness checks passed: 199 frozen contracts, 36 generic validation,
  18 finite-real realization and 80 native MathComp endpoints.
- The 12-module safe joint `coqchk -norec` completed successfully.
- Separate Gate M audit passed: 30 direct endpoints and 6 safe controls,
  including explicit unsafe-hierarchy reporting (not a universe-safe result).
- `git diff --check` passed. No CI or environment changes.
