#!/usr/bin/env python3
"""Phase 4b.4: exact approved algebra delegation; no carrier change yet.

The relocation manifest records every permitted source edit against 8610c68,
including proof-only repairs in two clients. It is not a regenerated compiled
baseline. The 505 maintained compiled contracts remain independently frozen.
"""
import argparse
import json
import re
import subprocess
from pathlib import Path
from audit_assumptions import query, logical_axioms, without_comments
from audit_rational_pruning import names

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '8610c68'
MANIFEST = ROOT / 'docs/FINITE_ALGEBRA_RELOCATION.json'
COMMON = ['theories/Prob/Backend/Common/' + n + '.v' for n in
          ['FiniteListAlgebra', 'FiniteAtoms', 'FiniteScalarMap']]
REGRESSION = 'theories/Regression/Backend/RationalFiniteAlgebra.v'
ADDED = set(COMMON + [REGRESSION])
AGGREGATE = 'theories/Regression/Infrastructure/AllImports.v'
POLICY = 'docs/CONTRACT_POLICY.json'


def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT).decode()


def replay(old, edits):
    lines = old.splitlines(keepends=True)
    end = len(lines) + 1
    for edit in reversed(edits):
        start = edit['start']
        before = edit['old'].splitlines(keepends=True)
        assert 0 <= start <= start + len(before) <= len(lines)
        assert start + len(before) <= end, 'Overlapping edits'
        assert lines[start:start + len(before)] == before, 'Wrong source anchor'
        lines[start:start + len(before)] = edit['new'].splitlines(keepends=True)
        end = start
    return ''.join(lines)


def common_boundary(source):
    code = without_comments(source)
    assert not re.search(r'\b(?:Axioms?|Parameters?|Admitted|admit|Class|Coercion|Instance)\b', code)
    assert not re.search(r'\b(?:Semantic\w*|FreeOmega|OmegaVal|ptree|nnQ|EnumQ|SubEnum\w*)\b', code)
    assert not re.search(r'Unset\s+(?:Universe|Guard|Positivity)\s+Checking|bypass_check', code)
    for line in code.splitlines():
        if 'PTree.' in line:
            assert line.startswith('From PTree.Prob.Backend.Common Require Import '), line


def check():
    manifest = json.loads(MANIFEST.read_text())
    assert manifest['baseline'] == BASELINE
    old_paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
                                        cwd=ROOT, text=True).splitlines()
    old_v = {p for p in old_paths if p.endswith('.v')}
    assert {p.relative_to(ROOT).as_posix() for p in (ROOT/'theories').rglob('*.v')} == old_v | ADDED
    for path in old_v:
        before = frozen(path)
        if path in manifest['edits']:
            expected = replay(before, manifest['edits'][path])
        elif path == AGGREGATE:
            lines = before.splitlines(keepends=True)
            extra = ['Require PTree.' + p.removeprefix('theories/').removesuffix('.v').replace('/', '.') + '.\n'
                     for p in ADDED]
            imports = iter(sorted([s for s in lines if s.startswith('Require PTree.')] + extra))
            expected = ''.join([next(imports) if s.startswith('Require PTree.') else s for s in lines] + list(imports))
        else:
            expected = before
        assert (ROOT/path).read_text() == expected, 'Unapproved theory change: ' + path
    for path in COMMON:
        common_boundary((ROOT/path).read_text())
    for path in old_paths:
        if path.startswith('docs/') and ('CONTRACT' in path or 'SNAPSHOT' in path) and path != POLICY:
            assert (ROOT/path).read_text() == frozen(path), 'Frozen contract changed: ' + path
    policy = json.loads((ROOT/POLICY).read_text())
    assert policy['regressions'].pop(REGRESSION) == names((ROOT/REGRESSION).read_text())
    assert policy == json.loads(frozen(POLICY))
    from audit_architecture import report
    assert (ROOT/'docs/ARCHITECTURE_AUDIT.md').read_text() == report()
    print('Exact algebra relocation: six clients, four new modules; other theory and contract snapshots unchanged.')


def compiled_check():
    endpoints = []
    for path in COMMON + [REGRESSION]:
        module = 'PTree.' + path.removeprefix('theories/').removesuffix('.v').replace('/', '.')
        endpoints += [module + '.' + n for n in names((ROOT/path).read_text(), 'Definition|Lemma|Theorem|Example|Fixpoint')]
    entries = query(endpoints)
    for entry in entries:
        allowed = set()
        if entry['name'].rsplit('.', 1)[-1] in {'ordinary_q_to_r_mass', 'ordinary_q_to_r_bind'}:
            allowed = {'boolp.propositional_extensionality',
                       'boolp.functional_extensionality_dep',
                       'boolp.constructive_indefinite_description'}
        assert logical_axioms(entry['assumptions']) <= allowed, entry
    print(f'{len(entries)} new declarations audited: shared algebra closed; '
          'only the two concrete rat-to-real regressions may use existing MathComp extensionality/choice.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-only', action='store_true')
    args = parser.parse_args()
    check()
    if not args.source_only:
        compiled_check()
