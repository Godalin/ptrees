#!/usr/bin/env python3
"""Container-nonnegativity obligations for the ordinary rational carrier."""
import argparse
import json
import re
import subprocess
from pathlib import Path
from audit_assumptions import query, logical_axioms
from audit_finite_algebra import common_boundary
from audit_rational_pruning import names

ROOT = Path(__file__).resolve().parents[1]
BASELINE = 'f9485be'
CLIENT = 'theories/Prob/Backend/SubEnumR/Coupling.v'
COMMON = 'theories/Prob/Backend/Common/FiniteSupport.v'
REGRESSION = 'theories/Regression/Backend/FiniteSupport.v'
AGGREGATE = 'theories/Regression/Infrastructure/AllImports.v'
POLICY = 'docs/CONTRACT_POLICY.json'


def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def adapted(source):
    marker = 'From PTree.Prob.Backend.SubEnumR Require Import Representation Measure.\n'
    assert source.count(marker) == 1
    source = source.replace(marker, marker + 'From PTree.Prob.Backend.Common Require Import FiniteSupport.\n')
    source, count = re.subn(r'(Lemma real_enum_expect_entry_le\b[\s\S]*?\n)Proof\.[\s\S]*?Qed\.',
                           lambda m: m[1] + 'Proof.\n  exact: finite_expect_entry_le.\nQed.', source)
    assert count == 1
    return source


def check():
    paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE], cwd=ROOT, text=True).splitlines()
    added = {COMMON, REGRESSION}
    assert {p.relative_to(ROOT).as_posix() for p in (ROOT/'theories').rglob('*.v')} == {p for p in paths if p.endswith('.v')} | added
    for path in paths:
        if not path.endswith('.v') and not (path.startswith('docs/') and ('CONTRACT' in path or 'SNAPSHOT' in path)):
            continue
        old = frozen(path)
        if path == CLIENT:
            expected = adapted(old)
        elif path == AGGREGATE:
            lines = old.splitlines(keepends=True)
            extra = ['Require PTree.' + p.removeprefix('theories/').removesuffix('.v').replace('/', '.') + '.\n' for p in added]
            imports = iter(sorted([s for s in lines if s.startswith('Require PTree.')] + extra))
            expected = ''.join([next(imports) if s.startswith('Require PTree.') else s for s in lines] + list(imports))
        elif path == POLICY:
            policy = json.loads((ROOT/path).read_text())
            assert policy['regressions'].pop(REGRESSION) == names((ROOT/REGRESSION).read_text())
            assert policy == json.loads(old)
            continue
        else:
            expected = old
        assert (ROOT/path).read_text() == expected, path
    common_boundary((ROOT/COMMON).read_text())
    from audit_architecture import report
    assert (ROOT/'docs/ARCHITECTURE_AUDIT.md').read_text() == report()
    print('Support conservation: one proof delegation; every other old theory file and contract frozen.')


def compiled_check():
    endpoints = []
    for path in [COMMON, REGRESSION]:
        module = 'PTree.' + path.removeprefix('theories/').removesuffix('.v').replace('/', '.')
        endpoints += [module+'.'+name for name in names((ROOT/path).read_text())]
    for entry in query(endpoints):
        allowed = set()
        if entry['name'].endswith('.real_positive_atom'):
            allowed = {'boolp.propositional_extensionality',
                       'boolp.functional_extensionality_dep',
                       'boolp.constructive_indefinite_description'}
        assert logical_axioms(entry['assumptions']) <= allowed, entry
    print(f'{len(endpoints)} endpoints audited: common/rat/universe closed; '
          'realType regression inherits only existing MathComp extensionality/choice.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-only', action='store_true')
    args = parser.parse_args()
    check()
    if not args.source_only:
        compiled_check()
