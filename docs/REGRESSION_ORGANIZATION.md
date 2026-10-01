# Examples and compilation tests

There is no maintained `theories/Regression/` namespace. Mathematical results
are organized by what they mean, not by the development stage that introduced
them. The root `opam exec -- dune build` compiles both the library/examples and
the standalone compilation tests. Tests are not an additional semantics.

## Where content belongs

| Content | Owner |
| --- | --- |
| Reusable parameterized semantic law | Its production module in Prob, Eq, Semantics, Interp or Execution |
| Program proof, probability calculation, supporting mathematical example | `theories/Examples/` |
| Substantive mathematical counterexample | `theories/Examples/Counterexamples/` |
| Independent external-model example or counterexample | `Examples/Validation/` or `Examples/Counterexamples/Validation/` |
| Import isolation/order, minimal capability inference, actual rewrite syntax, universe/assembly probe | `tests/` |
| A wrapper that merely applies an existing endpoint without testing a new boundary | Delete it |

Not every example is a paper case study. The existing flagship cases and their
reading order remain in [CASE_STUDIES.md](CASE_STUDIES.md). Supporting examples
have a separate topical directory; they need not mimic a program-rewriting
proof when their content is genuinely analytic or coinductive.

`Examples/Internal` exercises maintained auxiliary compression/scheduling/
recovery infrastructure. It does not make that machinery canonical semantics.
External-model examples remain one-way consumers: ordinary reasoning modules
and program examples may not import them. No production theory imports any
example or test; no example imports a test. These are checked dependency rules.

## Why a few compilation clients remain

`dune build` checks only the source contexts that actually exist. A file with
`Fail Check ...` asserts that a name is **absent** in its isolated import context;
one aggregate that imports everything cannot make that assertion. Similarly,
an explicit weak context checks that a theorem does not require stronger laws,
and an actual `setoid_rewrite` checks tactic usability, not just its Proper type.

These small clients live in physical `tests/`, with logical prefix `PTree.Tests`.
They are built by the same root command, but not installed as library theory.
`tests/AllImports.v` separately imports every other safe module exactly once.
Do not merge import-order probes into a single session, and do not grow this
directory into a second mathematical library. An occasional negative-import
assertion next to a mathematical example is harmless; primary content decides
ownership, not the mere presence of `Example` or `Fail`.

MathComp's permission remains an exact two-file exception:
`theories/Eq/Backend/MathComp.v` and `tests/MathComp.v`. The latter retains its
existing assembly/program probes together rather than spreading unchecked
code into new examples. Both are excluded from safe AllImports. No new file
inherits a bypass from its directory.

## Recorded reclassification from e9b5680

The completed reclassification and its move ledger are retained in Git.
For example, `git show 891932f:docs/REGRESSION_RECLASSIFICATION.json` retrieves
every old/new path, disposition, and intentional deletion/promotion. This is
review evidence, not a historical replay gate that freezes future edits.
The following counts describe that checkpoint, not the current inventory.

- 102 former Regression modules: 79 mathematical examples/counterexamples,
  23 compilation clients (including AllImports).
- No `.v` module is deleted merely to reduce the count. Nine redundant wrapper
  declarations are removed; their already-maintained theorem owners or stronger
  clients remain.
- `native_reflection_requires_left_unit` moves, with the same statement and
  proof, to `Prob/FreeOmega/NativeCoupling.v`. The deliberately faulty native
  model remains a mathematical counterexample, not a production backend.
- Retained source changes are import/qualified-name relocations and role
  comments, apart from those explicitly listed deletions/promotion. No probability
  definition, capability, canonical route or program semantics is redesigned.
- Snapshot relocation is mechanical. Only the two retired GenericAlgebra
  Proper wrappers lose compiled snapshot entries; their production counterparts
  remain audited. Logical-axiom whitelists are not broadened.

At that checkpoint the project had 433 Rocq modules, of which 431 are Gate S and two
are the explicitly unchecked Gate M. This is a responsibility change and a
small content diet, not a claim of having deleted 102 modules of mathematics.

| Source role | Before | After |
| --- | ---: | ---: |
| Production theory modules | 306 | 306 |
| Mathematical/program examples | 25 | 104 |
| Old Regression hierarchy | 102 | 0 |
| Standalone compilation clients (including aggregate) | 0 | 23 |

## Verification

Use the existing commands in [AUDITING.md](AUDITING.md). The source-layout
helper makes all current-tree checks inspect both roots. Architecture policy
rejects a new Regression namespace and enforces the example/test/model edges.
No new per-migration audit framework, environment change or CI query is needed.

The original local validation and exact-source comparison are retained with
the migration in Git. Current module counts come from
[the generated inventory](ARCHITECTURE_AUDIT.md), not the historical table above.
