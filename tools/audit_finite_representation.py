#!/usr/bin/env python3
"""Phase 2 only: additive common finite algebra, no native backend migration.

The accepted Phase 1 audit is left untouched. Compare all existing tracked
files with 2f3889a, allowing only three AllImports insertions, registration of
the new regression, and the regenerated architecture report. No snapshot is
regenerated. New common constants are checked independently for assumptions.
"""
import argparse
import json
import re
import subprocess
from pathlib import Path

from audit_assumptions import query, logical_axioms, without_comments, SOUNDNESS_AXIOMS

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '2f3889a'
ENUM = 'theories/Prob/Backend/Common/FiniteEnum.v'
SUBDIST = 'theories/Prob/Backend/Common/FiniteSubdist.v'
REGRESSION = 'theories/Regression/Probability/FiniteRepresentation.v'
NEW_THEORIES = {ENUM, SUBDIST, REGRESSION}
AGGREGATE = 'theories/Regression/Infrastructure/AllImports.v'
POLICY = 'docs/CONTRACT_POLICY.json'
REPORT = 'docs/ARCHITECTURE_AUDIT.md'


def frozen_files():
    return subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
                                   cwd=ROOT, text=True).splitlines()


def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT)


def inserted_imports(original):
    lines = original.decode().splitlines(keepends=True)
    added = ['Require PTree.' + p.removeprefix('theories/').removesuffix('.v').replace('/', '.') + '.\n'
             for p in NEW_THEORIES]
    imports = iter(sorted([line for line in lines if line.startswith('Require PTree.')] + added))
    result = []
    for line in lines:
        result.append(next(imports) if line.startswith('Require PTree.') else line)
    result.extend(imports)
    return ''.join(result).encode()


def regression_names(text):
    return re.findall(r'^(?:Example|Lemma|Theorem)\s+(\w+)', without_comments(text), re.M)


def preserved_file(path, old, new, regression):
    if path == AGGREGATE:
        assert new == inserted_imports(old), 'AllImports changed beyond explicit insertions'
    elif path == POLICY:
        actual, expected = json.loads(new), json.loads(old)
        assert actual['regressions'].pop(REGRESSION) == regression_names(regression), 'Incomplete new regression coverage'
        assert actual == expected, 'Old contract policy changed'
    else:
        assert new == old, 'Frozen source/contract changed: ' + path


def common_boundary(sources):
    for path in (ENUM, SUBDIST):
        code = without_comments(sources[path])
        assert not re.search(r'\b(?:Axiom|Axioms|Parameter|Parameters|Admitted|admit|Class)\b', code), path
        assert not re.search(r'\b(?:Semantic\w*|FreeOmega|OmegaVal|ptree|nnQ|Nonneg|SubEnum\w*|EnumQ|realType)\b', code), path
        assert not re.search(r'\bUnset\s+(?:Universe|Guard|Positivity)\s+Checking\b', code), path
        ptree_lines = [line.strip() for line in code.splitlines() if 'PTree.' in line]
        expected = [] if path == ENUM else ['From PTree.Prob.Backend.Common Require Import FiniteEnum.']
        assert ptree_lines == expected, 'Common algebra acquired a semantic/backend dependency'
        assert 'Variable R : numDomainType.' in code, 'Scalar requirement changed'
    enum, subdist = sources[ENUM], sources[SUBDIST]
    assert 'finite_enum_raw : list (R * A)' in enum
    assert 'finite_enum_nonnegative : finite_nonnegative finite_enum_raw' in enum
    assert 'finite_subdist_enum : FiniteEnum R A' in subdist
    assert 'finite_subdist_mass_bound : finite_mass finite_subdist_enum <= 1' in subdist


def check():
    paths = frozen_files()
    old_theories = {p for p in paths if p.endswith('.v')}
    actual = {p.relative_to(ROOT).as_posix() for p in (ROOT / 'theories').rglob('*.v')}
    assert actual == old_theories | NEW_THEORIES, 'Unexpected theory addition/deletion'
    regression = (ROOT / REGRESSION).read_text()
    for path in paths:
        if path != REPORT:
            preserved_file(path, frozen(path), (ROOT / path).read_bytes(), regression)
    common_boundary({p: (ROOT / p).read_text() for p in NEW_THEORIES})
    from audit_architecture import graph, report
    edges = graph()
    for module, deps in edges.items():
        new = {p.removeprefix('theories/').removesuffix('.v') for p in NEW_THEORIES}
        if module not in new | {AGGREGATE.removeprefix('theories/').removesuffix('.v')}:
            assert not (set(deps) & new), 'Backend migrated early: ' + module
    assert (ROOT / REPORT).read_text() == report(), 'Architecture report stale'
    print(f'Phase 2: {len(old_theories)} old theory modules preserved; only 3 new modules; '
          'snapshots, Phase 1 audit and all backend representations unchanged.')


def compiled_check():
    endpoints = []
    for path in sorted(NEW_THEORIES):
        code = without_comments((ROOT / path).read_text())
        names = re.findall(r'^(?:Definition|Fixpoint|Lemma|Theorem|Example|Record)\s+(\w+)', code, re.M)
        module = 'PTree.' + path.removeprefix('theories/').removesuffix('.v').replace('/', '.')
        endpoints.extend(module + '.' + name for name in names)
    entries = query(endpoints)
    regression_axioms = set()
    common_count = 0
    for entry in entries:
        axioms = logical_axioms(entry['assumptions'])
        if '.Common.' in entry['name']:
            # The shared finite algebra is constructive. The real sqrt
            # regression may inherit MathComp's existing classical foundation.
            assert not axioms, entry['name']
            common_count += 1
            assert 'ssrnum.Num.NumDomain.type' in entry['type'], entry['name']
            assert not re.search(r'\b(?:Semantic\w*|FreeOmega|OmegaVal|ptree|realType)\b', entry['type']), entry['name']
        else:
            assert axioms <= SOUNDNESS_AXIOMS, entry['name']
            regression_axioms |= axioms
    print(f'{common_count} common constants closed under the global context; '
          f'{len(entries) - common_count} regression constants within the existing logical whitelist.')
    print('Regression logical dependencies: ' + ', '.join(sorted(regression_axioms)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-only', action='store_true')
    args = parser.parse_args()
    check()
    if not args.source_only:
        compiled_check()
