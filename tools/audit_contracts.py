#!/usr/bin/env python3
"""Current compiled contracts, with explicit safe and unchecked query contexts.

No history access and no snapshot-update mode. Accepted snapshots are data,
not executable migration scripts. Every registered group runs in CI.
"""
import argparse
import json
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS
from audit_mathcomp_direct import query_direct
from mathcomp_direct_policy import GATE_M

MANIFEST = ROOT / 'docs/CONTRACT_SUITES.json'
ALLIMPORTS = 'PTree.Regression.Infrastructure.AllImports'


def load_suites():
    data = json.loads(MANIFEST.read_text())
    assert data['version'] == 1
    groups = data['groups']
    assert len(groups) == len({g['id'] for g in groups}), 'Duplicate suite id'
    referenced = set()
    fields = set()
    result = []
    for group in groups:
        assert group['context'] in {'owners', 'recorded', 'safe-joint', 'gate-m-joint', 'gate-m'}
        path = group['snapshot']
        assert path.startswith('docs/') and '..' not in path and path.endswith('CONTRACTS.json')
        referenced.add(path)
        field = group.get('field', 'endpoints')
        assert field in {'endpoints', 'direct'}
        assert (path, field) not in fields, 'Duplicate snapshot group'
        fields.add((path, field))
        snapshot = json.loads((ROOT / path).read_text())
        entries = snapshot[group.get('field', 'endpoints')]
        assert entries and len(entries) == len({e['name'] for e in entries}), group['id']
        unsafe = group['context'].startswith('gate-m')
        for e in entries:
            assert set(e) == ({'name', 'type', 'assumptions', 'unsafe_hierarchy',
                              'session_collapsed_universes'} if unsafe else {'name', 'type', 'assumptions'})
            assert logical_axioms(e['assumptions']) <= SOUNDNESS_AXIOMS | set(
                data['axiom_exceptions'].get(e['name'], [])), e['name']
            module = e['name'].rsplit('.', 1)[0].removeprefix('PTree.').replace('.', '/')
            if unsafe:
                assert e['session_collapsed_universes'] is True
                assert bool(e['unsafe_hierarchy']) == (module in GATE_M), e['name']
            else:
                assert module not in GATE_M, 'Unchecked endpoint in safe group: ' + e['name']
        result.append((group, snapshot, entries))
    # A newly added snapshot cannot silently be omitted from the runner.
    on_disk = {p.relative_to(ROOT).as_posix() for p in (ROOT / 'docs').glob('*CONTRACTS.json')}
    assert referenced == on_disk, ('Unregistered/missing snapshot', referenced ^ on_disk)
    for path in referenced:
        snapshot = json.loads((ROOT / path).read_text())
        assert {(path, k) for k in ['endpoints', 'direct'] if k in snapshot} <= fields, path
    contexts = {g['id']: g['context'] for g, _, _ in result}
    assert contexts['direct_iteration'] == contexts['iteration_algebra'] == 'safe-joint'
    assert contexts['contracts'] == 'recorded'
    names = {e['name'] for _, _, entries in result for e in entries}
    assert set(data['axiom_exceptions']) <= names
    for name in [
        'PTree.Eq.Bind.peutt_bind',
        'PTree.Prob.Backend.SubEnumQ.FreeOmega.JointSoundness.free_omega_qlift_sound',
        'PTree.Eq.Backend.StableHittingDomainSubEnumQ.stable_hitting_denotational_adequacy',
        'PTree.Interp.IterationUniform.ptree_peutt_iteration_uniform',
        'PTree.Regression.Semantics.PTreeUniformity.state_fold_into_ptree',
        'PTree.Regression.Semantics.PTreeUniformity.exception_fold_into_ptree',
    ]:
        assert name in names, 'Missing maintained endpoint: ' + name
    return result


def check_group(group, snapshot, entries):
    context = group['context']
    names = [e['name'] for e in entries]
    if context.startswith('gate-m'):
        actual = query_direct(names, joint=context == 'gate-m-joint')
    else:
        modules = [ALLIMPORTS] if context == 'safe-joint' else (
            snapshot['modules'] if context == 'recorded' else None)
        actual = query(names, modules)
    compare(entries, actual)
    print(f"{group['id']}: {len(entries)} exact type/assumption contracts ({context})", flush=True)


def check_protocol_boundary():
    """Retain the cause-sensitive negative test, separate from positive uniformity."""
    import subprocess
    script = '''
From PTree.Regression.Infrastructure Require Import AllImports.
From PTree.Core Require Import PTreeDefinition IterationLaws.
From ITree.Basics Require Import Basics Monad.
From PTree.Eq.Backend Require Import SubEnumQ.
From PTree.Interp.FreeOmega Require Import IterationAlgebra.
Set Universe Polymorphism.
Goal True. idtac "UNIFORM_BOUNDARY_START". Abort.
Definition unpackageable {F : Type -> Type} :
 @iteration_uniform (ptree F SubEnumQ) Monad_ptree MonadIter_ptree free_omega_ptree_eq1 :=
 fun I J A f g h => @free_omega_peutt_iter_uniform SubEnumQ _ _ _ _ _ _ F I J A f g h.
Goal True. idtac "UNIFORM_BOUNDARY_END". Abort.
'''
    result = subprocess.run(['opam', 'exec', '--', 'coqtop', '-quiet', '-R',
        '_build/default/theories', 'PTree'], cwd=ROOT, input=script,
        text=True, capture_output=True)
    assert result.returncode == 0, result.stderr
    assert result.stdout.count('UNIFORM_BOUNDARY_START') == 1
    assert result.stdout.count('UNIFORM_BOUNDARY_END') == 1
    errors = result.stdout + result.stderr
    assert errors.count('Error:') == 1 and 'universe inconsistency' in errors.lower(), errors
    print('Old protocol package rejected specifically by universe inconsistency; direct package checked positively.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--metadata-only', action='store_true')
    parser.add_argument('--gate', choices=['S', 'M', 'all'], default='all')
    parser.add_argument('--group', help='Check one named suite for local development')
    args = parser.parse_args()
    suites = load_suites()
    if args.group and args.group not in {g['id'] for g, _, _ in suites}:
        parser.error('Unknown group: ' + args.group)
    print(f'{len(suites)} registered query groups; no Git history required.', flush=True)
    if not args.metadata_only:
        for g, d, es in suites:
            gate = 'M' if g['context'].startswith('gate-m') else 'S'
            if (args.gate in ['all', gate]) and (not args.group or g['id'] == args.group):
                check_group(g, d, es)
        if args.gate != 'M' and not args.group:
            check_protocol_boundary()
            # Probability-level checks without stored stage snapshots, kept
            # separate from migration history and run in their own safe sessions.
            from audit_soundness import mathcomp_native_check, real_joint_check, generic_quotient_check
            mathcomp_native_check()
            real_joint_check()
            generic_quotient_check()
