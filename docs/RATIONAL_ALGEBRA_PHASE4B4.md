# Phase 4b.4 — shared finite algebra and scalar transport

Baseline: accepted `8610c68`. This is a preparation checkpoint, **not** the
production rational carrier switch. The overall consolidation goal stays open
and continues without an intermediate acceptance pause.

## Shared mathematics

`Common/FiniteListAlgebra.v` owns raw list scale/bind algebra, parameterized
by an ordinary multiplication function. Associativity, commutativity and unit
laws are explicit premises where needed, not new probability classes. Its
numeric specialization agrees exactly with the existing `finite_bind` and
`finite_weight_map`. Order, multiplicity and zero entries are retained.

`Common/FiniteAtoms.v` owns indicator atom mass and the finite atom-sum
formula for expectation. Additivity, scaling, bind and nonnegativity are
proved here. Arbitrary signed observables are allowed in the algebraic
equalities; no normalization or new equality/coupling relation is introduced.

`Common/FiniteScalarMap.v` maps ordinary coefficients along an order-preserving
ring morphism. It proves exact raw-data preservation of ret/zero/bind and
preservation of mapped expectations and mass. It lifts to `FiniteEnum` and
`FiniteSubdist` without proof-field equality or proof irrelevance. This is the
generic transport needed for the final `rat -> R` embedding, not a conversion
through `nnQ`.

## Current production clients

`EnumQ/Representation` delegates scale and bind to the raw shared algebra.
The delegation is definitionally the old recursion; the regression proves
both exact equations by reflexivity. `EnumQ/Bind` reuses the common algebra,
and `EnumQ/FinitePresentation` uses the common atom-sum theorem via two
coefficient-value bridge lemmas. Those bridge lemmas are proof facts, not a
second runtime carrier.

Three old proofs needed explicit operation equations/goal conversions in
place of broad reduction: the commutation proof, the measure left-unit proof,
and the conditional resampling/Bernoulli factory clients. Their statements
are unchanged. In particular, pruning, indexed coupling, semantic equality,
AE and all semantic instances retain their definitions.

The regression also checks duplicate/zero blocks in bind, atom mass, exact
`Qval` mapping, and the new ordinary `rat -> R` transport's mass and bind laws.
The production `subenumQ_to_R` implementation is **not yet migrated**.

## Preservation gate

`FINITE_ALGEBRA_RELOCATION.json` lists every permitted source edit against
`8610c68`, including the small reduction repairs. `audit_finite_algebra.py`
replays those edits exactly and freezes all other old theory files except
the sorted aggregate import insertion. Existing compiled contract snapshots
are not regenerated. The new modules are checked for dependency boundaries,
unfinished proofs, new axioms/classes and checker relaxations.

The new declaration audit checks 54 constants. Shared algebra is closed under
the global context. Only the two concrete real-valued regression endpoints
may inherit MathComp's existing propositional/dependent-functional
extensionality and constructive indefinite description. No new probability
or transport-existence assumption is introduced.

Earlier phase audit scripts are unchanged. Their exact-source unit tests
now exercise their respective accepted commits (`e8a7524`, `b49fcf3`,
`8610c68`), since subsequent authorized client edits cannot satisfy all
historical checkpoint gates simultaneously. The current tree is checked by
the new exact relocation gate and the long-term audits.

## Validation

Local validation commands:

```sh
opam exec -- dune build
python3 -m unittest discover -s tools -p 'test_*.py'
python3 tools/audit_architecture.py --check
opam exec -- python3 tools/audit_finite_algebra.py
opam exec -- python3 tools/audit_assumptions.py --check
opam exec -- python3 tools/audit_soundness.py --check
```

Full build (including AllImports), 116 tool tests, the exact source gate,
architecture and all 505 existing compiled contracts passed. The 54-constant
new declaration audit passed with the separate rat-to-real whitelist above.
The soundness audit also passed: 199 exact contracts, 36 generic quotient
endpoints, 18 finite-real joint endpoints and 80 native MathComp endpoints;
all existing logical-axiom whitelists are unchanged.

Targeted kernel checks passed for the three new Common modules, Representation,
Bind, FrontierLift, FinitePresentation and RationalFiniteAlgebra together;
a second joint check after the full build covers Disintegration,
OperationalBernoulliFactory and AllImports. Each uses `coqchk -norec`
for each named module. These check those module bodies and
trusts dependencies; it is not a whole-library recursive kernel audit.
Gate M and CI policy remain unchanged.

Counts: 287 -> 291 theory modules, 77 -> 78 regression modules,
285 -> 289 Gate S modules, 2 -> 2 Gate M modules.

## Remaining work

Production remains `EnumQ = list (nnQ * A)` with the old `SubEnumQ` wrapper.
Next comes the actual switch to `FiniteEnum rat` / `FiniteSubdist rat`,
including indexed coupling/support/validation clients. After that, isolate
`nnQ` as deprecated legacy and replace the concrete Q-to-R embedding with the
ordinary scalar map. Do not mark the proposal complete based on this checkpoint.
