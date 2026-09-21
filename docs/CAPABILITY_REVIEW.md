# Gate C: capability, context and import review

Source baseline: accepted `2af47aa`. This gate changes neither directory
ownership nor the Stage 1–4 semantic contracts. It does not start StateInterp,
the FreeOmega adequacy audit, or Gate D's whole-library kernel check.

## Scope and evidence

The [public index](CAPABILITY_PUBLIC_INDEX.md) covers **306 entries**:
all identifier aliases/definitions in the six curated facades/adapters,
the underlying syntax constructors, the explicitly listed expert modules'
Theorem/Corollary/global-instance endpoints, the original 25 Gate A entries,
and named proof-helper probes. Alias and defining constant can both occur;
306 is not a count of distinct mathematical theorems. `tools/audit_public_capabilities.py`
specifies the scope and checks it against the accepted source archive.
Symbolic notation is covered by its defining relation and existing parser
regressions. This is not a claim to audit every internal Lemma as public API.

The [before snapshot](CAPABILITY_GATE_C_BEFORE.json) was queried before each
audited declaration changed, using compiled `Check @...` and `Print Assumptions`.
The three PTreeKernel bridge probes were added before editing that module;
the already captured entries were preserved rather than re-baselined.
The [after snapshot](CAPABILITY_GATE_C_AFTER.json) retains complete types and
logical axiom types. Summary class names never replace carrier assignments,
return relations, handler contracts, or scheduling hypotheses.

The source-level check is independent: `audit_gate_c.py` compares every old
`.v` file with `2af47aa`. Its explicit transformation list permits the
reviewed context/import edits and exactly three simplified bridge proofs.
All other old proof bodies and local semantic contracts are preserved.
There is one new capability regression and its AllImports entry. Unlisted
source changes, added modules, or unproved declarations in that regression
fail. This is conservation of a reviewed delta, not a claim that a diff
checker can prove mathematical minimality.

## Actual theorem weakening

| Endpoint family | Before | After / proof reason |
| --- | --- | --- |
| `peutt_interp_structural` | native Core + AELift + Omega operations | Core + Omega operations; its unchanged proof uses `pstruct_interp` then `peutt_of_pstruct` |
| `peutt_translate_structural` | inherited native AELift | no AELift, via the structural interpretation endpoint |
| `ptree_primitive_hitting_adequate` | native interface/Core, behavioral Core/Bind, MixedLaws | behavioral Core alone among laws: both sides are the same approximant by definition, so use `sem_eq_refl` |
| `ptree_primitive_stable_hitting_adequate`, `ptree_primitive_ast_adequate` | additionally OmegaLaws and the finite bridge's laws | operations only, by definitional reflexivity; no native measure interface or measure laws |
| `peutt_translate` | native AELift inherited through the finite bridge | Core + Omega operations; its whole original coupling proof is unchanged |
| `peutt_translate_Proper`, `peutt_translate_id`, `peutt_interp_trigger`, `peutt_translate_compose` | inherited native AELift | Core + Omega operations, through the repaired bridge/translation proof |

These are ten changed compiled types, not ten new theorems. The three
adapter bridges had become definitionally equal when primitive hitting
became canonical; their old proof reconstructed equations unnecessarily.
This is not an adequacy theorem for realizing arbitrary FreeOmega measures
in a concrete backend. That separate audit remains deferred.

The logical audit also detects a real improvement: `peutt_translate`, its
Proper/identity/composition endpoints, and `peutt_interp_trigger` no longer
depend on functional extensionality. The old helper path instantiated
unneeded FreeOmega bind/mixed laws carrying that dependency. Their remaining
`eq_rect_eq` dependency is unchanged. All other audited logical assumption
lists are unchanged; the checker permits exactly these five removals and
rejects additions or other differences.

No requirement for arbitrary handler preservation is weakened into an
unconditional congruence. Guardedness, atomic inverse-label/Dirac contracts,
MDP fragment hypotheses and the explicit atomic `Htotal_map` remain intact.
The original 25 Gate A endpoint types/assumptions remain a separate check.

## Source Context hygiene (not theorem strengthening)

- Remove unused native AELift Context from FreeOmega `Base`, `Relation`,
  `Iter`, and interpreter `Cofinality`. Rocq already omitted it from their
  constants. Removing it documents the real boundary, not a new theorem.
- After the bridge fix, remove AELift from `Translate` and the interpreter's
  translation identity/composition Sections. Here the compiled type really
  does change, as listed above.
- Remove unused native `SemanticMeasure MN` contexts from `Interp/Kernel`
  and the two sections of `Eq/ProbabilisticTrace`. They use behavioral `MF`
  operations and the mixed adapter, not native operations. Their elaborated
  types already expressed this independence.
- Move the legacy Monad/MonadMeasure contexts below `stuckE`, keeping them
  around `stuckM`. Both exported types are unchanged; this does not conflate
  weighted score programs with subprobabilistic PTree validity.

Do not shrink a mixed Section's Context merely because an early declaration
does not use every law. For example Algebra's structural equations need
only Core, but its behavioral bind/fmap Proper instances need AELift,
CouplingAE and CountableAE. Their full types make this distinction explicit.
No new bundled class or opaque instance hides those requirements.

## Proof-helper and retained-premise review

The linked source and per-entry full types are the detailed endpoint record;
this table records the reasoning by proof family, including why capabilities
were retained rather than removed on textual-name heuristics.

| Public family / source | Actual helper path | Decision |
| --- | --- | --- |
| Core and probability validity (`API/Generic`, `Eq/WellFormedness`) | syntax operations; unary well-formedness coinduction and constructor closure | keep probability laws distinct from arbitrary carrier operations; no measure package is added to Core |
| `pstruct`, `pstrong`, their bind/iter/equivalence laws | structural GFP, relational lift composition, `pstruct_iter_rel`/naturality/codiagonal/split | no weakening of related-branch or barrier hypotheses; native Core for coupling stays explicit |
| generic hitting existence / uniqueness | `sem_lub_exists` on the increasing chain / `sem_lub_unique` | existence needs Order + OmegaLaws; uniqueness only OmegaLaws in its actual type, not the entire shared Context |
| Ret/Vis/Tau/Prob computation (`PTreeKernel`, `StableHittingComputation`) | `sem_bind_ret_l`, mixed associativity/AE congruence, prefix/cofinality, mixed omega law | retain packages used by these actual calculations; Dirac and nested-Prob laws still require MixedUnit / NodeBind respectively |
| `peutt` GFP and equivalence | `stable_hitting_match`, monotonicity, coupling converse/composition | no separation or totality added to generic equivalence; existing dependent inversion assumptions are reported |
| generic `peutt_bind` | `ptree_stable_hitting_bind`, front choice, diagonal lub, bind-lift | cofinality remains a local hypothesis; generic MN/MF theorem is not passed off as an unconditional concrete theorem |
| FreeOmega bind/cofinality and algebra | two-budget approximation bounds, `ptree_bind_cofinal_all`, `peutt_of_pstruct`, behavioral bind | retain funext in budget identities; structural equations do not need AE, behavioral Proper does |
| FreeOmega iter | structural iter algebra; Ret-only grid/limit proof for eventless fusion; eventful generator-closed certificate | remove unused AELift, retain CouplingAE/CountableAE on the eventless route and the actual `no_event` or closure premise; do not claim unconditional eventful behavioral fusion |
| generic interpreter kernel | `sem_bind_diagonal_lub` and increasing source/head chains | native interface unused; behavioral Diagonal/Order/cofinality requirements remain |
| interpreter structural laws | `pstruct_interp`, bind/iter/compose/handler laws, `peutt_of_pstruct` | structural rewrite does not need native AELift; no assumption on handler productivity is invented |
| behavioral translation | approximation cofinality, quotient composition, definitional primitive bridge | the identified overstrong bridge is fixed; full helper proof otherwise retained |
| guarded interpretation | hitting uniqueness → `free_omega_qlift_support`; AE restriction → `sem_lift_bind`; visible head → bind-up-to → fusion | retain native CouplingAE/CountableAE for support and diagonal proofs, AELift for behavioral bind/mixed law instances; `Hguard` remains explicit, not a global search obligation |
| atomic interpretation | `atomic_start/finish`, `atomic_interp_head_hitting`, action inversion and totalized observations | retain inverse label contract, support laws and AELift: the Ret case still calls the non-definitional Ret-hitting computation law requiring behavioral BindLaws |
| `mdp_handler` / `mdp_state_interp` | chosen head contract, interp-hitting composition, uniqueness, quotient bind | contract needs Core; preservation needs Core + CouplingAE + CountableAE, not AELift; genuine `E -> F` boundary unchanged |
| guarded/atomic MDP compositionality | source coincidence → guarded interp → target coincidence; unary atomic head invariant | retain guardedness/fragment hypotheses and generic total-map premise; atomic profile remains `E -> E` |
| `head_bisim`, `tree_trans_bisim`, soundness | independent GFPs; return/event projections and AE-restricted action-kernel bind | no peutt hidden in relation definitions; Order is retained on existence of matching witnesses, not assumed as an enabledness condition |
| MDP coincidence / embedding | Dirac AE inversion, distribution-pair candidate, successor totality and support; encoding kernel | generic Dirac/totality capabilities remain explicit; FreeOmega provides its Dirac AE fact; SubEnum reflection stays concrete, not promoted to arbitrary measures |
| finite interaction observations | branch choice, query-related induction, coupling uniqueness, epsilon-selected representative | native interface unused; bind/support/order/omega obligations depend on endpoint; chosen representative still only unique up to equality coupling |
| Enum/SubEnum probability and interpreter endpoints | denominator/indicator expectation, `subenum_bound`, concrete total-map realization | zero class parameters mean instantiated backend, not assumption-free numerics; SubEnum range remains `[0,1]`, legacy weighted Enum is not silently bounded |

Retention in this table means required by the checked proof and current
capability packages, **not** a mathematical impossibility of finding a
different proof under weaker hypotheses. In particular no new smaller law
class was introduced just to make a parameter count look better.

## Imports and architecture

53 explicit Require references were removed from existing files. Copied
blanket imports were removed from FreeOmega Base/Relation/Bind/Iter,
interpreter Cofinality/Translate, and generic Interp/Kernel. Required direct
owners remain: e.g. PeanoNat in Translate and PrimitiveStableHitting in
Cofinality were retained after compile checks. Removing a `Require` that is
still loaded transitively does not establish logical-axiom independence;
the compiled assumption audit is separate.

The curated FreeOmega facade imports the actual owners of its aliases,
not unused Base/Relation assemblies. The comparison facade no longer loads
MDPCoincidence just to expose transition/fragment definitions. No alias,
notation, module ownership or bulk-export contract is added or removed.

FiniteInternal is untouched. Its existing formal-mainline dependency
exclusion remains machine checked; eventual liveness/deletion is deferred.

## Regression and validation

`Regression/Infrastructure/CapabilityBoundaries.v` uses Sections **without**
native AELift to check structural interpretation, structural and behavioral
translation, interp cofinality, and generic heterogeneous MDP preservation.
A separate section checks the complete-hitting adapter with no measure laws
and no native interface. The existing facade and Stage 1–4 regressions remain
part of the full build. These checks are not public theory endpoints.

All checks below completed successfully locally: full `dune build`, the
209-module import inventory, ownership/dependency and source-delta audits,
historical Gate B/follow-up conservation, the original 25-entry comparison,
the 306-entry before/after audit, all 26 audit-tool tests, and the regenerated
layout report. The same-process **17-module targeted kernel check** also
completed successfully with exit status 0; it checks the changed formal
modules and the capability/facade/AllImports harnesses, not every proof in
all 209 modules. No new axioms or admitted proofs were introduced.

Reproduction commands:

```sh
opam exec -- dune build
python3 tools/check_aggregate.py
python3 tools/audit_gate_c.py
python3 tools/audit_migration.py --revision 2af47aa
python3 tools/audit_architecture.py --check
python3 tools/audit_capabilities.py --check --compare-baseline
python3 tools/audit_public_capabilities.py --check
python3 -m unittest discover -s tools -p test_audit_tools.py
python3 tools/audit_layout.py
opam exec -- coqchk -silent -R _build/default/theories PTree \
  -norec PTree.API.FreeOmega -norec PTree.API.Weighted \
  -norec PTree.Eq.FreeOmega.Algebra -norec PTree.Eq.FreeOmega.Base \
  -norec PTree.Eq.FreeOmega.Bind -norec PTree.Eq.FreeOmega.Iter \
  -norec PTree.Eq.FreeOmega.Relation -norec PTree.Eq.PTreeKernel \
  -norec PTree.Eq.ProbabilisticTrace -norec PTree.Interp.FreeOmega.Base \
  -norec PTree.Interp.FreeOmega.Cofinality -norec PTree.Interp.FreeOmega.Translate \
  -norec PTree.Interp.Kernel -norec PTree.Semantics \
  -norec PTree.Regression.Infrastructure.CapabilityBoundaries \
  -norec PTree.Regression.Infrastructure.ArchitectureBoundaries \
  -norec PTree.Regression.Infrastructure.AllImports
```

The historical migration audit intentionally names its frozen target;
running it without `--revision` still checks the working tree strictly and
will reject the authorized Gate C proof/context edits. Gate D is not claimed
complete, and no remote CI result is implied by local checks.
Gate C is submitted for acceptance; stop here before Gate D or new theory.
