# Compilation clients

Run `opam exec -- dune build` from the repository root. No separate Rocq test
command is required. This directory uses logical namespace `PTree.Tests` and
is not installed with the library.

Keep only isolated import/order, minimal capability, actual rewriting, and
universe/assembly checks here. Mathematical examples and counterexamples
belong in `theories/Examples`; reusable laws belong at their formal owner.
Neither production theory nor examples may import these clients.

`AllImports.v` checks safe joint loading; it intentionally excludes the exact
Gate M pair. `MathComp.v` is the existing locally unchecked assembly client,
not permission to disable universe checking elsewhere in `tests/`.

See the [policy and recorded reclassification](../docs/ARCHITECTURE.md#examples-and-tests).
