# Discrete two-level distributions: implementation checkpoints

Baseline: `28ae229`. Local validation only; CI is deliberately out of scope.

`MN` supplies native discrete sampling; `MF` supplies stable frontiers. The
generic tree theory assumes neither `MF = MN` nor `MF = FreeOmega MN`.
The independent expectation domain validates representations; it is not a
third project-wide distribution parameter or another free probability syntax.

## Existing completion capabilities

`Regression/Backend/BackendCapabilities.v` now checks the following with an
arbitrary native carrier, in separately scoped capability contexts. These
are existing implementations, not newly assumed mathematical laws.

Every row below has native `SemanticMeasure`, `CoreLaws`, and `SemanticOmega`
operations available. **Native `SemanticOmegaLaws` and native `BindLaws` are
not prerequisites.** Availability of a native lub relation must not be
confused with completeness of that relation (finite native carriers need
not contain all countable limits).

| Completed capability | Additional native requirement |
| --- | --- |
| Core, order, omega, total properness, cofinality, mixed omega | none |
| Bind and mixed bind | AE lifting |
| Mixed unit | Dirac AE |
| Nested native sampling / mixed node bind | Bind AE exactness |
| Fubini | Coupling AE |
| Diagonal, omega AE, coupling AE | Coupling AE + countable AE |

Commutativity remains optional. This table records sufficient, compiled
dependency profiles, not a claim of mathematical minimality.

## Work sequence and boundaries

1. Freeze the generic capability probes and baseline validation.
2. Add native-parametric external validation with AE-sensitive sample/bind
   closure; preserve the existing internal `free_omega_denotes` name and meaning.
3. Connect the existing SubEnum interpretation without changing DS1--DS5
   statements or replacing the qlift proof through inadmissible intermediates.
4. Develop finite-real native distributions, reusing generic completion work.
5. Audit/prove MathComp direct `MN = MF` capabilities before claiming the
   remaining obstacle is universe-level. Ordinary bind, relational bind,
   omega completeness and coupling gluing are separate obligations.

No unsafe universe experiment is part of the trusted theory. No such
experiment has been introduced at this checkpoint. Existing soundness,
partial-mass and invalid-raw-lub regressions remain authoritative.

### Capability checkpoint validation

Full local `dune build` (including AllImports), architecture/API/source audits,
all 48 tool tests, and the 505-entry compiled signature/assumption snapshot
passed. A targeted `coqchk -norec` of BackendCapabilities passed; this is not
a new recursive whole-library kernel audit. No CI claim is made.
