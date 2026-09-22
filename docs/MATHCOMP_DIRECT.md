# Direct MathComp: trust boundary and capability probes

Baseline: `bb927a5`. This is the first direct-backend increment, NOT final
backend acceptance. Existing native mathematics and generic PTree theory
are unchanged. No CI work or environment changes are included.

## Goal and current status

The intended direct pair is `MN = MF = MathCompKernelMeasure R`. The removed
MathComp + FreeOmega combination stays removed. The two normally checked,
complete behavioral backends remain SubEnum/FreeOmega and SubEnumR/FreeOmega.

| Direct capability | Current result |
| --- | --- |
| Native same-carrier mixed operation | Reuse checked MathCompNativeMixedMeasure |
| PTree, stable head, measure of stable heads | Compiles with explicit universe bypass |
| Primitive kernel and stable-hitting predicate | Compiles with explicit universe bypass |
| peutt and generic eventful reflexivity | Compiles; MathCompCouplingGluing remains explicit |
| Native SemanticMeasureOrderLaws | Missing; negative inference probe |
| Native SemanticOmegaLaws | Missing; negative inference probe |
| General stable-hitting existence | Pending both preceding law packages |
| Native Bernoulli / bind / recursive cross-checks | Pending; not replaced by reflexivity |

The negative existence probe applies the actual generic
`ptree_stable_hitting_exists` with holes for exactly the order/omega packages.
There is no assumed instance making this endpoint appear complete.
Reflexivity alone does not establish existence: its generic proof matches
whatever complete witnesses exist, without requiring a witness for every tree.

The next mathematical work belongs in checked native modules: source-side
bind monotonicity, increasing-chain lub existence and laws, and required bind
continuity. Existing native order basics and continuation monotonicity are
already available. Do not add unrelated capabilities for symmetry.

## Exact trust split

Gate S is every source module except these two Gate M entries:

- `Eq/Backend/MathComp/Direct.v`: assembly using already checked operations and
  theorems, located under Eq because it consumes PTree/Eq theory.
- `Regression/Backend/MathCompDirect.v`: explicit direct-backend client/probes.

Only these exact files may contain exactly one
`Local Unset Universe Checking.` command. Native MathComp modules, generic
theory, finite backends, Domain, other regressions and examples may not use it.
No safe module may import either Gate M module, directly or transitively.
Every Gate M client must depend on the direct assembly. New entries require
changes to the explicit policy, its test and compiled snapshot.

Safe `Regression/Infrastructure/AllImports.v` remains byte-for-byte unchanged
and covers all 267 Gate S modules (including itself), not the two new Gate M
modules. Ordinary `dune build` builds both groups in separate compiler
processes; it must NOT be reported as a universe-checked whole-library build.
The gate runner also offers an explicit safe-only build target list.

Loading Gate M into the existing all-imports universe environment also needs
the bypass at the client import site. The dedicated Gate M audit loads safe
AllImports first, then explicitly disables checking before requiring the
direct modules. No safe audit uses that session or command.

## Reliability claim, and its limit

Native measure-theoretic proofs and generic PTree proofs remain independently
universe-checked. Gate M instantiates them at a universe combination rejected
by the normal checker. Even a short `exact existing_theorem` is not proof
that the rejected universe instantiation is consistent.

Coq 8.20 reports both per-declaration `relies on an unsafe hierarchy` lines
and `Theory: Type hierarchy is collapsed (logic is inconsistent)`. The latter
also appears for safe facts queried in the unchecked session; it describes
the current session, not necessarily that constant. Our separate snapshot
records both categories verbatim in structured form, preserves the existing
logical-axiom whitelist, and checks that native control constants have no
per-declaration unsafe flags. Unknown output/errors fail the audit.

Gate M is explicitly **not** a universe-consistency result or a normal
kernel-checked endpoint. Future concrete cross-checks will compare meanings
but will not repair this logical trust gap. No new probability axiom, class,
carrier, completion, quotient, or public API is introduced here.

## Local verification

```sh
python3 tools/audit_mathcomp_direct.py --gate S --build
python3 tools/audit_assumptions.py --check
python3 tools/audit_soundness.py --check
python3 tools/audit_api.py --check --surface-only
python3 tools/audit_architecture.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
python3 tools/audit_mathcomp_direct.py --gate M --build
```

Gate S's normal targeted kernel check can include native Measure/NativeLaws,
the checked MathCompUniverse regression and BackendCapabilities. Gate M's
compiled snapshot is separate (`MATHCOMP_DIRECT_CONTRACTS.json`); it never
replaces the frozen 505 normal contracts. No Gate M kernel-consistency pass
is claimed. The checked negative universe regression remains in Gate S.

## First-increment verification result

- Full local `dune build`: passed, 269 modules = 267 Gate S + 2 Gate M.
- Explicit Gate S target build and safe AllImports: passed.
- All 505 frozen compiled signatures/assumptions unchanged.
- Full soundness check: 199 frozen, 36 generic validation, 18 finite-real
  realization and 22 native MathComp endpoints passed with the existing
  logical-axiom whitelist.
- Curated API, architecture and source checks: passed; all 67 tool tests passed.
- Gate M: 14 direct endpoints plus 2 native controls matched the separate
  compiled type/assumption/unsafe-hierarchy snapshot, in a session that first
  loads safe AllImports. Safe controls have no unsafe declaration flags.
- Four-module joint targeted `coqchk` passed for native Measure, NativeLaws,
  MathCompUniverse and BackendCapabilities, using `-norec` for those four
  modules (dependencies trusted). This is not recursive whole-library Gate D.
- No existing mathematical definition, theorem statement or proof changed;
  the only existing `.v` edit is the MathCompUniverse role comment.
- No new probability assumption/class, public facade change, completion,
  environment change or CI action.

This completes the isolation/probe increment only. Native order/omega proofs,
general direct hitting existence and nontrivial semantic cross-checks remain
open; complete direct-backend acceptance is not claimed.
