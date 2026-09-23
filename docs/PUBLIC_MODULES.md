# Public module reorganization

Baseline: accepted `33cb5d8`. This is a module/notation/ownership migration,
not a new probability or equivalence theory. CI is intentionally ignored.

## Entry points

```coq
From PTree Require Import PTree.       (* construct programs *)
From PTree Require Import Eq.          (* relations and their notation *)
From PTree Require Import PTreeFacts.  (* usual equational/interpreter facts *)
From PTree.Eq.Backend Require Import SubEnumQ. (* choose this native profile *)
```

`PTree` exports Core/PTreeDefinition and its combinator/notation modules.
`Eq` directly exports PStruct, PStrong, PEutt and Canonical, then their three
notation modules. `PTreeFacts` exports the program/relation entry points,
stable-hitting/validity/observation theory, FreeOmega Bind/Algebra/Iter and
Guarded/Atomic/MDP interpreter theory. None loads a concrete backend.

There is no `theories/API/` directory, forwarding module, replacement alias
facade or compatibility shim. The existing independent comparison entry point
`Semantics.v` is unchanged; it is not part of the removed API namespace.

| Previous owner | Current owner / disposition |
| --- | --- |
| API/Behavior | Eq/Canonical |
| API/BehaviorFreeOmega | Eq/FreeOmega/Canonical |
| API/EnumQ route | Eq/Backend/EnumQ |
| API/SubEnumQ route | Eq/Backend/SubEnumQ |
| API/SubEnumR route | Eq/Backend/SubEnumR |
| API/Generic, API/FreeOmega aliases | Removed; import/export actual theorem owners |
| API/Weighted | Removed, no actual source clients |

Backend route modules export the native representation so `SubEnumQ` can be
used directly by an ordinary client; mathematical definitions and laws remain
in Prob. Eq/Backend/SubEnumQ does **not** import Interp; its former interpreter
alias is replaced by the actual `Interp/Backend/SubEnumQ` owner.

## Relations and bind

| Owner | Notation module | Relation |
| --- | --- | --- |
| Eq/PStruct | PStructNotations | `≡ₚ`, `≡ₚ[RR]` → pstruct |
| Eq/PStrong | PStrongNotations | `≃ₚ`, `≃ₚ[RR]` → pstrong |
| Eq/Canonical | PEuttNotations | `≈ₚ`, `≈ₚ[RR]` → canonical_peutt |

Raw `PEutt.peutt` is still the generic relation. The thin CanonicalBehavior
selector still has only MF/FI/MX/FO operations, no laws or blanket route.
The complete observable expansion is checked definitionally for EnumQ,
SubEnumQ and SubEnumR in three independent import orders. Structural
FreeOmega registrations remain local.

The only unconditional `peutt_bind` is now the existing heterogeneous
`Eq/FreeOmega/Bind.peutt_bind`. The raw generic theorem has the descriptive
name `Eq/PEutt.peutt_bind_cofinal`. Its statement and proof are unchanged
modulo this identifier rename, including the cofinality premise. Its internal
references and the FreeOmega corollary's call are updated, with no old-name
alias. Consequently even importing raw PEutt **after** PTreeFacts cannot
shadow the unconditional theorem. No export-order trick or tactic magic is
needed.

The public-only regression imports `PTree PTreeFacts` and `Eq.Backend.SubEnumQ`
and proves heterogeneous bind with `eapply peutt_bind; eassumption`, or
`apply (peutt_bind (RR := RR)); assumption`. RR remains premise-only; naked
`apply` is intentionally rejected. Further tests cover heterogeneous Ret for
all three notations, Tau/reflexivity, and bind after the raw-owner import.

Direct owner exports intentionally expose helpers declared in those modules,
such as `ptree_bind_cofinal_all`. The old facade's short-name hiding is **not**
preserved. What is preserved and tested is the semantic dependency boundary:

- importing PTree alone loads no PTree probability interface or relation;
- Eq does not load FreeOmega bind or interpreter theory;
- PTreeFacts loads no concrete carrier, Eq/Internal or external Domain;
- safe entries do not load the unchecked MathComp route.

Existence checks use `Check @constant`, avoiding unconstrained typeclass
search when the selected theorem module exposes an implicitly parameterized
helper. This changes tests, not proof-theory hints.

## Removed convenience declarations

The old EnumQ `meas/kernel/sampleE/handle_sample`, SubEnumQ
`submeas/subkernel/subSampleE/handle_subsample`, and Weighted `stuckE/stuckM`
had no actual theorem/program clients. Their ten frozen contracts are
explicitly retired; generated constructors/schemes of the two removed sample
event wrappers disappear with those wrappers. No native probability operation
or proof is removed. All deleted code is recoverable at the baseline commit.

## Preservation ledger

`public_module_migration.py` reads the **frozen baseline**, not current compiler
output, to derive the new expected contract file. It resolves every former
facade alias to its actual owner, applies the explicit module and bind-name
relocations, and accounts for the ten removals. If two old aliases map to one
owner, their expected type/assumptions must agree before deduplication.

```text
505 old contract entries
  - 10 deliberately retired convenience contracts
  - 30 duplicate alias entries consolidated at the same owner
  = 465 distinct contracts
      266 public/helper + 199 soundness
      (all original 25 capability probes retained)
```

The sole additional printer qualification adjustment is
`@Backend.SubEnumQ.subenumQ_mdp_state_interp_atomic` becoming
`@SubEnumQ.subenumQ_mdp_state_interp_atomic` after the competing API module is
removed. The endpoint remains fully qualified to the same Interp owner;
its parameters, conclusion and assumptions are not changed.

`audit_public_modules.py` checks 217 retained production modules against the
baseline, allowing only the declared module imports/relocations, the raw bind
identifier rename and the three notation modules (comments/whitespace ignored).
The concrete route constant bodies are retained; their short assembly preludes
are fixed explicitly. It rejects a second `peutt_bind` owner, a competing glyph
owner, API namespace resurrection and alias definitions in the three new main
entry points. Unmodified mathematical modules cannot acquire new declarations
or changed proofs under this gate.

The original routing registry/structural-registration checks remain active,
after inverse owner-path mapping. Historical `audit_behavior_routing.py` and
`audit_public_behavior.py` remain checkpoint-specific; their expected source
is not weakened to accommodate this migration. The latter's mutation tests
now exercise its accepted `33cb5d8` source; current-module tests are separate.

## MathComp and logical trust

The two existing Gate M files only change their selector import to
`Eq/Canonical`. Eq now follows its ordinary dependency direction; the old
Eq-to-API exception is removed, not broadened. There are still exactly two
allowlisted universe-unchecked modules. Native mathematics stays checked.

The Gate M snapshot changes only the relocated selector's printed namespace.
All 32 direct endpoints, six safe controls, logical assumptions and
unsafe-hierarchy flags remain checked. This is not a universe-safe assembly
claim. No Axiom, class, coercion, inference hint or checker bypass is added.

## Local validation

```sh
opam exec -- dune build
python3 tools/audit_public_modules.py --compiled --kernel
python3 tools/audit_api.py --surface-only
python3 tools/audit_soundness.py --check
python3 tools/audit_architecture.py --check
python3 tools/audit_mathcomp_direct.py --gate M
python3 -m unittest discover -s tools -p 'test_*.py'
```

The joint kernel target is 20 safe module bodies with `-norec`: dependencies
are loaded but not recursively rechecked. Gate M is excluded. This is not
Gate D, a whole-library kernel audit or a remote CI result.

Completed locally for this migration:

- Full `dune build`, including safe `AllImports`, passed.
- All 465 relocated compiled contracts matched the frozen expected types and
  assumptions; 25 public/import-order endpoints also passed.
- The joint 20-module `coqchk -norec` check passed.
- Architecture, public surface and soundness audits passed, including 199
  soundness contracts, 36 generic validation endpoints, 18 real-joint endpoints
  and 80 MathComp native endpoints.
- Gate M's 32 direct endpoints and six safe controls retained their recorded
  types, logical assumptions and unsafe-hierarchy flags.
- All 139 Python tool tests passed. No remote CI was queried or claimed.

The repository goes from 306 to 305 theory modules: eight API files disappear,
five owner modules and two top-level aggregates replace them. Case studies,
FreeOmega mathematics, external validation and probability backends are not
redesigned by this migration.
