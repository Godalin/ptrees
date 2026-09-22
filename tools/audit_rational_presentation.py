#!/usr/bin/env python3
"""Phase 4b.3: exact finite-presentation extraction from frozen b49fcf3.

Old compiled contracts are independently replayed, not recaptured. This gate
belongs to this checkpoint; earlier checkpoint audits are left unchanged.
"""
import argparse
import json
import re
import subprocess
from pathlib import Path
from audit_assumptions import query, logical_axioms
from audit_rational_positions import endpoint_query
from audit_rational_pruning import names, common_boundary

ROOT = Path(__file__).resolve().parents[1]
BASELINE = 'b49fcf3'
CLIENT = 'theories/Prob/Backend/EnumQ/FinitePresentation.v'
COMMON = 'theories/Prob/Backend/Common/FinitePresentation.v'
REGRESSION = 'theories/Regression/Backend/RationalPresentation.v'
AGGREGATE = 'theories/Regression/Infrastructure/AllImports.v'
POLICY = 'docs/CONTRACT_POLICY.json'
REPORT = 'docs/ARCHITECTURE_AUDIT.md'
MODULE = 'PTree.Prob.Backend.EnumQ.FinitePresentation'


def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT)


def adapted(source):
    source = source.replace('\nSet Implicit Arguments.',
        '\nFrom PTree.Prob.Backend.Common Require Import FinitePresentation.\n\nSet Implicit Arguments.', 1)
    source = source.replace('\n\nFrom PTree.Prob.Backend.Common Require Import FinitePresentation.',
        '\nFrom PTree.Prob.Backend.Common Require Import FinitePresentation.', 1)
    for old, new in [
        ("Definition enumQ_position {A} (mu : EnumQ A) := 'I_(size mu).",
         'Definition enumQ_position {A} (mu : EnumQ A) := finite_position mu.'),
        ('  tnth (in_tuple mu) i.', '  finite_position_entry mu i.'),
        ('Definition enumQ_position_weight {A} (mu : EnumQ A) i := (enumQ_position_entry mu i).1.',
         'Definition enumQ_position_weight {A} (mu : EnumQ A) (i : enumQ_position mu) := finite_position_weight mu i.'),
        ('Definition enumQ_position_value {A} (mu : EnumQ A) i := (enumQ_position_entry mu i).2.',
         'Definition enumQ_position_value {A} (mu : EnumQ A) (i : enumQ_position mu) := finite_position_value mu i.'),
        ('  finite_weighted_enumQ (enumQ_position_weight mu) id.', '  finite_positions mu.'),
    ]:
        assert source.count(old) == 1
        source = source.replace(old, new)
    source, n = re.subn(r'(^Lemma enumQ_positions_decode\b[\s\S]*?\n)Proof\.[\s\S]*?Qed\.',
        lambda m: m[1] + 'Proof. exact: finite_positions_decode. Qed.', source, count=1, flags=re.M)
    assert n == 1
    return source


def client_check(old, new):
    assert new == adapted(old), 'Unapproved client change'


def check():
    paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE], cwd=ROOT, text=True).splitlines()
    added = {COMMON, REGRESSION}
    assert {p.relative_to(ROOT).as_posix() for p in (ROOT / 'theories').rglob('*.v')} == {
        p for p in paths if p.endswith('.v')} | added
    for path in paths:
        old, actual = frozen(path), (ROOT / path).read_bytes()
        if path == REPORT:
            continue
        if path == CLIENT:
            client_check(old.decode(), actual.decode())
        elif path == AGGREGATE:
            lines = old.decode().splitlines(keepends=True)
            new = ['Require PTree.' + p.removeprefix('theories/').removesuffix('.v').replace('/', '.') + '.\n' for p in added]
            imports = iter(sorted([line for line in lines if line.startswith('Require PTree.')] + new))
            result = [next(imports) if line.startswith('Require PTree.') else line for line in lines]
            assert actual.decode() == ''.join(result + list(imports))
        elif path == POLICY:
            policy = json.loads(actual)
            assert policy['regressions'].pop(REGRESSION) == names((ROOT / REGRESSION).read_text())
            assert policy == json.loads(old)
        else:
            assert actual == old, 'Frozen source/snapshot/tool changed: ' + path
    common_boundary((ROOT / COMMON).read_text())
    from audit_architecture import report
    assert (ROOT / REPORT).read_text() == report()
    print('Phase 4b.3: five definition delegations and one shared proof; '
          'all old coupling/transport proofs, other backend sources and snapshots unchanged.')


def normalize(text):
    return ' '.join(text.replace('Phase4bPresentationBaseline.', 'FinitePresentation.').split())


def compare(old, new):
    assert len(old) == len(new)
    for a, b in zip(old, new):
        assert a['name'] == b['name']
        for field in ('type', 'assumptions'):
            assert normalize(a[field]) == normalize(b[field]), (a['name'], field, a[field], b[field])


def compiled_check():
    source = frozen(CLIENT).decode()
    declarations = names(source, 'Definition|Lemma|Theorem')
    endpoints = [MODULE + '.' + n for n in declarations]
    prefix, body = source.split('Definition enumQ_position ', 1)
    current = endpoint_query('Require ' + MODULE + '.\n' + prefix, endpoints, endpoints)
    reference = (prefix + '\nModule Phase4bPresentationBaseline.\nDefinition enumQ_position '
                 + body + '\nEnd Phase4bPresentationBaseline.\n')
    baseline = endpoint_query(reference, endpoints, ['Phase4bPresentationBaseline.' + n for n in declarations])
    compare(baseline, current)
    print(f'{len(endpoints)} client declarations: compiled types and assumptions match replayed {BASELINE}.')
    fresh = []
    for path in (COMMON, REGRESSION):
        module = 'PTree.' + path.removeprefix('theories/').removesuffix('.v').replace('/', '.')
        fresh += [module + '.' + name for name in names((ROOT / path).read_text(), 'Definition|Lemma|Theorem|Example')]
    for entry in query(fresh):
        assert not logical_axioms(entry['assumptions']), entry
    print(f'{len(fresh)} new shared/regression constants: closed under the global context.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-only', action='store_true')
    args = parser.parse_args()
    check()
    if not args.source_only:
        compiled_check()
