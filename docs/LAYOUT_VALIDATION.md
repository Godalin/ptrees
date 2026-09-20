# Layout milestone validation

The cleanup preserves the theory baseline `92e0841`. Its scope and exhaustive
path/client inventory are in [LAYOUT_AUDIT.md](LAYOUT_AUDIT.md).

## Passed local checks

- `opam exec -- dune clean`, followed by a full `opam exec -- dune build`.
  A further full build passed after the final MathComp support-file move.
  The old `Examples` build tree is absent.
- `python3 tools/audit_layout.py`: all 190 Coq modules match the baseline
  after namespace normalization, with zero added/deleted declarations or
  changed proofs. The stored report reproduces byte-for-byte.
- All 65 moved modules and all nine `Semantics` modules passed `coqchk`
  **in separate processes**: 74/74. No source fix or axiom was used to obtain
  these results. Native-computation tests may emit the standard VM fallback
  warning when native compilation is disabled.
- `git diff --check` and the staged equivalent passed.
- No legacy `PTree.Examples` imports remain in maintained Coq sources.
  Core/Prob/Eq/Semantics have no dependencies on cases or regressions;
  cases have no regression dependencies.

The per-module kernel checks can be reproduced from the manifest:

```sh
python3 - <<'PY'
import csv
import subprocess
from pathlib import Path

with Path('docs/module-moves.tsv').open() as manifest:
    paths = [r['new_path'] for r in csv.DictReader(manifest, delimiter='\t')]
paths += [str(p) for p in sorted(Path('theories/Semantics').glob('*.v'))]
for path in paths:
    module = 'PTree.' + path.removeprefix('theories/').removesuffix('.v').replace('/', '.')
    subprocess.run(['opam', 'exec', '--', 'coqchk', '-silent',
                    '-R', '_build/default/theories', 'PTree',
                    '-norec', module], check=True)
    print('PASS', module, flush=True)
PY
```

## Aggregate-check limitation

An additional attempt to pass all 74 modules to **one** `coqchk` process
failed with `Universe inconsistency`. Separate checks of every one of those
modules then passed. The full build also passes, but these facts do not
establish that all independent case/regression modules can be jointly loaded
into a single universe context.

The conflicting subset and whether the same aggregate conflict occurs at
the pre-migration baseline were not determined. This is recorded, not
silently counted as a passing check. Resolving aggregate-import compatibility
must be a separate audit; this milestone does not change universe declarations,
theorem statements or proofs to make that extra check pass.

These are local results. No remote CI success is asserted here.
