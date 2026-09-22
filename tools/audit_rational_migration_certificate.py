#!/usr/bin/env python3
"""Phase 4a only: exact representation certificate, NOT backend migration.

Freeze all 280 old theories and every previous contract/tool byte-for-byte.
Only add one regression, its aggregate import and contract registration.
The actual Phase 4 carrier replacement must use a subsequent, separate gate.
"""
import argparse
import json
import re
import subprocess
from pathlib import Path

from audit_assumptions import logical_axioms, query, without_comments

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '683d3c7'
CERTIFICATE = 'theories/Regression/Backend/RationalRepresentationMigration.v'
AGGREGATE = 'theories/Regression/Infrastructure/AllImports.v'
POLICY = 'docs/CONTRACT_POLICY.json'
REPORT = 'docs/ARCHITECTURE_AUDIT.md'
MODULE = 'PTree.Regression.Backend.RationalRepresentationMigration'


def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT)


def declarations(source, kinds='Lemma|Theorem|Example'):
    return re.findall(r'^(?:' + kinds + r')\s+(\w+)', without_comments(source), re.M)


def aggregate(old):
    lines = old.decode().splitlines(keepends=True)
    imports = [line for line in lines if line.startswith('Require PTree.')]
    imports.append('Require ' + MODULE + '.\n')
    assert len(imports) == len(set(imports))
    ordered = iter(sorted(imports))
    result = [next(ordered) if line.startswith('Require PTree.') else line for line in lines]
    return ''.join(result + list(ordered)).encode()


def preserved(path, old, new, source):
    if path == AGGREGATE:
        assert new == aggregate(old), 'Only the certificate import is authorized'
    elif path == POLICY:
        actual, expected = json.loads(new), json.loads(old)
        assert actual['regressions'].pop(CERTIFICATE) == declarations(source)
        assert actual == expected, 'Existing contract policy changed'
    else:
        assert old == new, 'Frozen file changed: ' + path


def boundary(source):
    code = without_comments(source)
    assert not re.search(r'\b(?:Axiom|Axioms|Parameter|Parameters|Admitted|admit|Class|CoInductive)\b', code)
    assert not re.search(r'\bUnset\s+(?:Universe|Guard|Positivity)\s+Checking\b|bypass_check', code)
    assert not re.search(r'\b(?:Coercion|Canonical|Instance|Existing)\b', code), 'No compatibility instance/coercion'
    assert not re.search(r'\b(?:ProofIrrelevance|proof_irrelevance|Classical\w*)\b', code)
    for theorem in ['rational_old_roundtrip', 'rational_shared_roundtrip',
                    'rational_shared_bind', 'rational_shared_index', 'rational_shared_ae',
                    'rational_shared_expect', 'rational_shared_subprob',
                    'rational_sub_old_roundtrip', 'rational_sub_shared_roundtrip',
                    'rational_subshared_bind', 'rational_partial_mass_preserved',
                    'rational_high_carrier']:
        assert theorem in declarations(source), 'Missing migration obligation: ' + theorem


def check():
    paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
                                    cwd=ROOT, text=True).splitlines()
    source = (ROOT / CERTIFICATE).read_text()
    boundary(source)
    for path in paths:
        if path != REPORT:
            preserved(path, frozen(path), (ROOT / path).read_bytes(), source)
    old = {p for p in paths if p.endswith('.v')}
    current = {p.relative_to(ROOT).as_posix() for p in (ROOT / 'theories').rglob('*.v')}
    assert current == old | {CERTIFICATE}, 'Unexpected theory addition/deletion'
    from audit_architecture import graph, report
    owner = CERTIFICATE.removeprefix('theories/').removesuffix('.v')
    for module, deps in graph().items():
        if module != 'Regression/Infrastructure/AllImports':
            assert owner not in deps, 'Migration certificate became a library dependency: ' + module
    assert (ROOT / REPORT).read_text() == report(), 'Architecture report stale'
    print(f'Phase 4a: {len(old)} old theories preserved; one isolated migration certificate. '
          'No backend representation switched; all previous snapshots/tools unchanged.')


def compiled_check():
    names = declarations((ROOT / CERTIFICATE).read_text(), 'Definition|Fixpoint|Lemma|Theorem|Example')
    entries = query([MODULE + '.' + name for name in names])
    for entry in entries:
        assert not logical_axioms(entry['assumptions']), entry
    print(f'{len(entries)} migration constants checked: closed under the global context.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-only', action='store_true')
    args = parser.parse_args()
    check()
    if not args.source_only:
        compiled_check()
