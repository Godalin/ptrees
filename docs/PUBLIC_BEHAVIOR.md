# Public canonical behavioral notation and bind

Historical accepted checkpoint: `33cb5d8`. For the current module ownership,
see [PUBLIC_MODULES.md](PUBLIC_MODULES.md); this report records the prior gate.

Baseline: accepted routing foundation `a95734e`. This gate changes the public
notation/API, not the mathematical relations or backend capabilities. CI is
intentionally out of scope.

## Surface and ownership

`API/Generic` alone owns `≈ₚ` and `≈ₚ[RR]`. Both expand through
`API/Behavior.canonical_peutt`, hence select MF, FI, MX and FO together and
then obtain CoreLaws for that selected FI. `Eq/PEutt` no longer declares a
competing glyph. Its raw `PEutt.peutt` remains fully parameterized; the facade
also retains the advanced raw `peutt` alias. No blanket route, new typeclass,
projection instance, coercion or semantic definition is introduced.

`API/FreeOmega` now exposes `peutt_bind` as a direct alias of the existing
heterogeneous `Eq/FreeOmega/Bind.peutt_bind`. This is the theorem which already
discharges bind cofinality for observable FreeOmega. There is no new proof and
no hidden additional scheduling premise.

`API/Generic.peutt_bind` retains the raw theorem and its explicit cofinality
premise, preserving its existing contract for arbitrary-frontier theory
clients. An arbitrary operation-only selector does not imply bind congruence.
`PTree` exports `API/FreeOmega` after `API/Generic`, so its public short name
selects the unconditional corollary; the minimal client tests this resolution.
The public
FreeOmega corollary applies definitionally to the registered EnumQ, SubEnumQ
and SubEnumR profiles. It is **not** advertised as a theorem for every
`CanonicalBehavior`; MathComp keeps its existing direct endpoint. `PTree`
already exports both curated facades, so ordinary PTree clients need no extra
implementation import.

## Public-only heterogeneous client

The independently compiled `Regression/Infrastructure/PublicBehavior.v`
imports exactly:

```coq
From PTree Require Import PTree.
From PTree.API Require Import SubEnumQ.
```

For arbitrary event signature, four return carriers and two relations:

```coq
Ht : t1 ≈ₚ[RR] t2
Hk : forall x y, RR x y -> k1 x ≈ₚ[RS] k2 y
-------------------------------------------------
bind t1 k1 ≈ₚ[RS] bind t2 k2
```

the checked proof is:

```coq
eapply peutt_bind; eassumption.
```

or, with the source relation specified:

```coq
apply (peutt_bind (RR := RR)); assumption.
```

**Acceptance-script qualification:** the originally requested bare
`apply peutt_bind; assumption` cannot infer RR: RR occurs only in the
premises, not in the bind conclusion. The regression records `Fail apply
peutt_bind` before the successful proof, rather than silently claiming the
literal script passed. Maximal implicit arguments do not solve this ordinary
Rocq elaboration issue. No tactic shadowing, context-search hint or relation
guessing is installed to hide it. The public-import and heterogeneous-relation
requirements are met; accepting the standard `eapply` spelling is an explicit
review point.

The same minimal client also checks reflexivity, Tau and heterogeneous Ret.
Three separate import-order files check all three finite routes by
`reflexivity` against the **complete explicit observable** raw peutt term;
they additionally check heterogeneous EnumQ/SubEnumR bind and reject notation
for an arbitrary native carrier with no registered selector. Neither these
clients nor the public facade load the MathComp Gate M route.

## Conservation and validation

`tools/audit_public_behavior.py` takes a new, fixed baseline `a95734e`;
`audit_behavior_routing.py` is not relaxed or rebased. Of 305 existing theory
modules, only these production edits are permitted (comments ignored):

- `Eq/PEutt`: remove precisely the two raw notation declarations;
- `API/Generic`: import the selector, change precisely the two notation
  expansions (all existing generic aliases retained);
- `API/FreeOmega`: explicitly import Bind and expose its existing corollary.

All other production source is byte-for-byte frozen, including every selector,
backend adapter, mathematical theorem/proof and both Gate M modules. The
three full-profile regressions preserve their explicit RHS and reflexivity
proofs. Other changes are the facade regression, one new public-only client,
AllImports, reviewed facade/test policy, documentation and audit tooling.

Both `CONTRACTS.json` (505 contracts) and
`MATHCOMP_DIRECT_CONTRACTS.json` remain byte-for-byte unchanged. The new gate
checks public endpoint assumptions against the existing backend logical-axiom
whitelist plus the exact frozen FreeOmega bind assumptions. That existing
behavioral theorem already depends on `RelationalChoice.relational_choice`
and `ClassicalUniqueChoice.dependent_unique_choice`; these are not new axioms
and the external-domain whitelist is not widened. The public bind alias is
separately required to have exactly the frozen corollary's compiled type and
assumptions. No semantic contract is regenerated.

Local validation commands:

```sh
opam exec -- dune build
python3 tools/audit_public_behavior.py --compiled --kernel
python3 tools/audit_assumptions.py --check
python3 tools/audit_api.py --surface-only
python3 tools/audit_soundness.py --check
python3 tools/audit_architecture.py --check
python3 tools/audit_mathcomp_direct.py --gate M
python3 -m unittest discover -s tools -p 'test_*.py'
```

The new joint kernel check targets 13 safe module bodies with `-norec`;
dependencies are loaded but not recursively rechecked. It excludes Gate M.
The separate Gate M audit retains the existing unsafe-hierarchy reporting.

Completed locally: full build/AllImports (306 modules: 304 Gate S, two Gate M);
505 unchanged compiled contracts; 21 public/client assumption checks plus an
exact frozen-type/assumption comparison of the public bind alias; architecture,
curated API and soundness audits; 134 tool tests; and the 13-module joint kernel
check above. The separate Gate M check passes for its unchanged 32 direct
endpoints and six safe controls. This is not a recursive whole-library kernel
audit, a universe-safe Gate M claim, or a remote CI result.

## Remaining notation work

`≡ₚ` / `≃ₚ`, a systematic public Proper/subrelation alignment, and ordinary
example migration are not performed in this gate. No mathematical completion,
new backend or probability-model work is mixed into this surface change.
