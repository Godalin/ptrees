#!/usr/bin/env python3
"""Phase 4b.2 checkpoint: exact pruning extraction, not a carrier migration.

Independently replay the frozen FrontierLift source to compare every compiled
declaration (including instances). Historical phase gates remain unchanged.
"""
import argparse
import json
import re
import subprocess
from pathlib import Path

from audit_assumptions import without_comments, query, logical_axioms
from audit_rational_positions import endpoint_query

ROOT = Path(__file__).resolve().parents[1]
BASELINE = 'e8a7524'
CLIENT = 'theories/Prob/Backend/EnumQ/FrontierLift.v'
COMMON = 'theories/Prob/Backend/Common/FinitePruning.v'
REGRESSION = 'theories/Regression/Backend/RationalPruning.v'
AGGREGATE = 'theories/Regression/Infrastructure/AllImports.v'
POLICY = 'docs/CONTRACT_POLICY.json'
REPORT = 'docs/ARCHITECTURE_AUDIT.md'
MODULE = 'PTree.Prob.Backend.EnumQ.FrontierLift'


def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT)


def names(source, kinds='Lemma|Theorem|Example'):
    return re.findall(r'^(?:#\[global\] )?(?:' + kinds + r')\s+(\w+)', without_comments(source), re.M)


def adapted(source):
    source = source.replace('From PTree.Prob.Interface Require Import FrontierLift.',
        'From PTree.Prob.Interface Require Import FrontierLift.\n'
        'From PTree.Prob.Backend.Common Require Import FinitePruning.', 1)
    source, n = re.subn(r'^Fixpoint enumQ_prune\b[\s\S]*?  end\.',
        '''Definition enumQ_prune {A} (mu : EnumQ A) : EnumQ A :=
  finite_prune (fun p => p == PTree.Prob.Backend.Common.RatSubTypes.nnQ_0) mu.''', source, count=1, flags=re.M)
    assert n == 1
    for name, proof in {
        'enumQ_prune_app': 'Proof. exact: finite_prune_app. Qed.',
        'enumQ_prune_emap': 'Proof. exact: finite_prune_map. Qed.',
        'enumQ_prune_in_source': '''Proof.
  move/finite_prune_in=> [Hin Hp]. split; first exact Hin.
  move=> Heq. subst p. by rewrite eq_refl in Hp.
Qed.''',
    }.items():
        source, n = re.subn(r'(^Lemma ' + name + r'\b[\s\S]*?\n)Proof\.[\s\S]*?Qed\.',
            lambda m: m[1] + proof, source, count=1, flags=re.M)
        assert n == 1
    for indent, hypotheses in [('  ', 'Hmn, Hkh'), ('    ', 'Hmn, HP, HQ, Hkh')]:
        old = indent + 'cbn in ' + hypotheses + ' |- *. rewrite !enumQ_prune_bind.'
        new = (indent + 'change (indexed_coupling S (enumQ_prune (bind_EnumQ mu k))\n'
               + indent + '  (enumQ_prune (bind_EnumQ nu h))).\n'
               + indent + 'rewrite !enumQ_prune_bind.')
        assert source.count(old) == 1
        source = source.replace(old, new)
    return source


def client_check(old, new):
    assert new == adapted(old), 'Unapproved client change'


def common_boundary(source):
    code = without_comments(source)
    assert not re.search(r'\b(?:Axiom|Axioms|Parameter|Parameters|Admitted|admit|Class|Coercion|Instance)\b', code)
    assert not re.search(r'\b(?:Semantic\w*|FreeOmega|OmegaVal|ptree|nnQ|EnumQ|SubEnum\w*|coupling|realType)\b', code)
    assert not re.search(r'Unset\s+(?:Universe|Guard|Positivity)\s+Checking|bypass_check', code)
    assert [line.strip() for line in code.splitlines() if 'PTree.' in line] == [
        'From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.']


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
    print('Phase 4b.2 source conservation: one pruning extraction, three shared proofs, '
          'two explicit goal conversions; all relations, signatures and old snapshots unchanged.')


def normalize(text):
    return ' '.join(text.replace('Phase4bPruneBaseline.', 'FrontierLift.').split())


def compare(old, new):
    assert len(old) == len(new)
    for a, b in zip(old, new):
        assert a['name'] == b['name']
        for field in ('type', 'assumptions'):
            assert normalize(a[field]) == normalize(b[field]), (a['name'], field, a[field], b[field])


def compiled_check():
    source = frozen(CLIENT).decode()
    declarations = names(source, 'Definition|Fixpoint|Lemma|Theorem|Instance')
    endpoints = [MODULE + '.' + name for name in declarations]
    prefix, body = source.split('Lemma nnq_mul_ne_zero', 1)
    current = endpoint_query('Require ' + MODULE + '.\n' + prefix, endpoints, endpoints)
    reference = prefix + '\nModule Phase4bPruneBaseline.\nLemma nnq_mul_ne_zero' + body + '\nEnd Phase4bPruneBaseline.\n'
    baseline = endpoint_query(reference, endpoints, ['Phase4bPruneBaseline.' + n for n in declarations])
    compare(baseline, current)
    print(f'{len(endpoints)} FrontierLift declarations (including instances): compiled types and assumptions match replayed {BASELINE}.')
    fresh = []
    for path in (COMMON, REGRESSION):
        module = 'PTree.' + path.removeprefix('theories/').removesuffix('.v').replace('/', '.')
        fresh += [module + '.' + name for name in names((ROOT / path).read_text(), 'Definition|Fixpoint|Lemma|Theorem|Example')]
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
