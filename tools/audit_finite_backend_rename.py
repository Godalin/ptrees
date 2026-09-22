#!/usr/bin/env python3
"""Phase 1 only: exact naming migration from the accepted ba509e1 archive.

No proof/representation normalization is used for Rocq sources. The only
extra source operation is sorting the renamed AllImports list. Compiled
snapshots may reflow whitespace, but must retain every token after renaming.
This audit is intentionally phase-specific, not a permanent representation
constraint on the later consolidation phases.
"""
import argparse
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASELINE = 'ba509e1'
WORD = re.compile(r'\b[A-Za-z_][A-Za-z_0-9]*\b')
LEGACY_UNCHANGED = {
    'theories/Prob/Legacy/Discrete.v',
    'theories/Prob/Legacy/Monad.v',
    'theories/Prob/Legacy/MonadList.v',
}
SNAPSHOTS = {'docs/CONTRACTS.json', 'docs/MATHCOMP_DIRECT_CONTRACTS.json'}
AGGREGATE = 'theories/Regression/Infrastructure/AllImports.v'
REPORT = 'docs/ARCHITECTURE_AUDIT.md'


def rename_word(word):
    # MathComp enumeration operations are not rational backend identifiers.
    if word in {'big_enum', 'index_enum', 'mem_enum', 'map_tnth_enum'} or word.startswith('real_enum'):
        return word
    word = re.sub(r'SubEnum(?!Q|R(?![a-z]))', 'SubEnumQ', word)
    word = re.sub(r'(?<!Sub)Enum(?![a-zQ])', 'EnumQ', word)
    word = re.sub(r'(?<![A-Za-z0-9])subenum(?=_|$)', 'subenumQ', word)
    word = re.sub(r'(?<![A-Za-z0-9])enum(?=_|$)', 'enumQ', word) if word != 'enum' else word
    return {'enumRT': 'enumQRT', 'enumk': 'enumQk', 'enumeq': 'enumQeq',
            'subenumE': 'subenumQE'}.get(word, word)


def rename(text):
    text = WORD.sub(lambda m: rename_word(m.group()), text)
    return re.sub(r'(?<=with )enum(?=\.)|(?<=%)enum\b', 'enumQ', text)


def map_json(value):
    if isinstance(value, str):
        return rename(value)
    if isinstance(value, list):
        return [map_json(v) for v in value]
    if isinstance(value, dict):
        return {rename(k): map_json(v) for k, v in value.items()}
    return value


def frozen_files():
    return subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
                                   cwd=ROOT, text=True).splitlines()


def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT)


def expected(path, raw):
    if path in LEGACY_UNCHANGED or not path.endswith(('.v', '.md', '.py', '.json')):
        return raw
    text = raw.decode()
    if path.endswith('.json'):
        return (json.dumps(map_json(json.loads(text)), indent=2, ensure_ascii=False) + '\n').encode()
    text = rename(text)
    if path == AGGREGATE:
        lines = text.splitlines(keepends=True)
        imports = iter(sorted(line for line in lines if line.startswith('Require PTree.')))
        text = ''.join(next(imports) if line.startswith('Require PTree.') else line for line in lines)
    return text.encode()


def apply_rename():
    # Bulk mechanical rewrite only. Refuse to overwrite any unreviewed edits.
    paths = frozen_files()
    targets = [rename(p) for p in paths]
    assert len(targets) == len(set(targets)), 'Module/path rename collision'
    plans = []
    for old, new in zip(paths, targets):
        src, dst = ROOT / old, ROOT / new
        raw = frozen(old)
        assert src.read_bytes() == raw, 'Dirty baseline file: ' + old
        assert old == new or not dst.exists(), 'Target already exists: ' + new
        plans.append((old, new, expected(old, raw)))
    for old, new, data in plans:
        src, dst = ROOT / old, ROOT / new
        if old != new:
            dst.parent.mkdir(parents=True, exist_ok=True)
            src.rename(dst)
        if dst.read_bytes() != data:
            dst.write_bytes(data)
    print('Applied pure naming migration; no representation changes.')


def whitespace_only(value):
    if isinstance(value, str):
        return ' '.join(value.split())
    if isinstance(value, list):
        return [whitespace_only(v) for v in value]
    if isinstance(value, dict):
        return {k: whitespace_only(v) for k, v in value.items()}
    return value


def check_snapshot(path, actual):
    want = map_json(json.loads(frozen(path)))
    assert whitespace_only(actual) == whitespace_only(want), \
        'Compiled contract changed beyond rename/printing whitespace: ' + path


def refresh_contracts():
    """Refresh line wrapping only after a token-exact frozen comparison."""
    from audit_assumptions import query
    from audit_mathcomp_direct import query_direct
    updates = []
    for path in sorted(SNAPSHOTS):
        data = map_json(json.loads(frozen(path)))
        if path.endswith('MATHCOMP_DIRECT_CONTRACTS.json'):
            data['endpoints'] = query_direct()
        else:
            data['endpoints'] = query([e['name'] for e in data['endpoints']], data['modules'])
        check_snapshot(path, data)
        updates.append((path, data))
    # Do not partially update if either gate has a non-whitespace difference.
    for path, data in updates:
        (ROOT / path).write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')
    print('Both compiled snapshots verified against frozen renamed tokens; refreshed printing whitespace only.')


def check():
    paths = frozen_files()
    theories = {rename(p) for p in paths if p.endswith('.v')}
    actual = {p.relative_to(ROOT).as_posix() for p in (ROOT / 'theories').rglob('*.v')}
    assert actual == theories, 'Theory module added/deleted outside pure rename'
    for old in paths:
        new = rename(old)
        if old != new:
            assert not (ROOT / old).exists(), 'Old compatibility path remains: ' + old
        if old in SNAPSHOTS:
            check_snapshot(old, json.loads((ROOT / new).read_text()))
        elif old != REPORT:
            assert (ROOT / new).read_bytes() == expected(old, frozen(old)), \
                'Not an exact naming migration: ' + old
    # Source conservation implies identical dependency statements. Independently
    # check the generated current graph and its frozen module/edge counts.
    from audit_architecture import report
    current = report()
    assert (ROOT / REPORT).read_text() == current, 'Architecture report stale'
    old_counts = re.search(r'(\d+) modules; (\d+) direct local Require edges', frozen(REPORT).decode()).groups()
    assert re.search(r'(\d+) modules; (\d+) direct local Require edges', current).groups() == old_counts
    print(f'Phase 1: all {len(theories)} Rocq modules exact modulo naming/AllImports sorting; '
          'frozen snapshots, tools and ownership preserved; no compatibility aliases.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--apply', action='store_true', help='one-time mechanical rewrite from clean baseline')
    mode.add_argument('--refresh-contracts', action='store_true', help='verify frozen contracts before refreshing line wrapping')
    args = parser.parse_args()
    if args.apply:
        apply_rename()
    elif args.refresh_contracts:
        refresh_contracts()
    else:
        check()
