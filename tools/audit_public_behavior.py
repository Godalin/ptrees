#!/usr/bin/env python3
"""Public notation gate against accepted routing foundation a95734e.

The earlier exact-source gate remains historical and is not relaxed here.
No compiled snapshot regeneration and no new semantic theorem or assumption.
"""
import argparse
import json
import re
import subprocess
from audit_assumptions import ROOT, without_comments, query, logical_axioms, SOUNDNESS_AXIOMS
from audit_behavior_routing import registry_check, structural_check, frozen, STRUCTURAL

BASELINE = 'a95734e'
PEUTT = 'theories/Eq/PEutt.v'
GENERIC = 'theories/API/Generic.v'
FREEOMEGA = 'theories/API/FreeOmega.v'
CLIENT = 'theories/Regression/Infrastructure/PublicBehavior.v'
PROBES = ['CanonicalBehavior', 'CanonicalBehaviorNativeFirst', 'CanonicalBehaviorStructuralFirst']
PROBE_PATHS = {'theories/Regression/Infrastructure/' + n + '.v' for n in PROBES}
FACADE_TEST = 'theories/Regression/Semantics/PublicSemanticFacade.v'
AGGREGATE = 'theories/Regression/Infrastructure/AllImports.v'


def historical(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def tokens(text):
    return ' '.join(without_comments(text).split())


def production_check(path, old, new):
    if path == PEUTT:
        old, count = re.subn(r'Notation "t ≈ₚ[^\n]*\n[^\n]*: type_scope\.', '', old)
        assert count == 2
    elif path == GENERIC:
        old = old.replace('Require Import UnifiedFrontier PrimitiveStableHitting PStruct PStrong PEutt StableHittingComputation ProbabilisticTrace.',
                          'Require Import UnifiedFrontier PrimitiveStableHitting PStruct PStrong PEutt StableHittingComputation ProbabilisticTrace.\nFrom PTree.API Require Import Behavior.')
        old = old.replace(':= (peutt RR t u)', ':= (Behavior.canonical_peutt RR t u)')
        old = old.replace(':= (peutt eq t u)', ':= (Behavior.canonical_peutt eq t u)')
    elif path == FREEOMEGA:
        old = old.replace('Require Import Algebra Iter.', 'Require Import Bind Algebra Iter.')
        old = old.replace('Notation peutt_bind_assoc', 'Notation peutt_bind := Bind.peutt_bind.\nNotation peutt_bind_assoc', 1)
    assert tokens(new) == tokens(old), 'Unapproved production change: ' + path


def client_check(source):
    code = without_comments(source)
    imports = re.findall(r'^From .*?\.$', code, re.M)
    assert imports == ['From PTree Require Import PTree.', 'From PTree.API Require Import SubEnumQ.'], imports
    assert not re.search(r'^\s*Require\b|\b(?:Instance|Existing|Coercion|Arguments|Hint)\b', code, re.M)
    for phrase in ['Fail apply peutt_bind.', 'eapply peutt_bind; eassumption.',
                   'apply (peutt_bind (RR := RR)); assumption.',
                   'bind t1 k1 ≈ₚ[RS] bind t2 k2']:
        assert phrase in code, 'Missing public contract: ' + phrase
    assert 'Eq.FreeOmega.Bind' not in code


def source_check():
    sources = {p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')}
    paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE], cwd=ROOT, text=True).splitlines()
    old_paths = {p for p in paths if p.endswith('.v')}
    assert set(sources) == old_paths | {CLIENT}, 'Unreviewed theory addition/deletion'
    changed_tests = PROBE_PATHS | {FACADE_TEST, AGGREGATE}
    for path in old_paths - changed_tests:
        if path in {PEUTT, GENERIC, FREEOMEGA}:
            production_check(path, historical(path), sources[path])
        else:
            assert sources[path] == historical(path), 'Frozen source changed: ' + path
    for path in ['docs/CONTRACTS.json', 'docs/MATHCOMP_DIRECT_CONTRACTS.json']:
        assert (ROOT/path).read_text() == historical(path), 'Frozen snapshot changed: ' + path
    # Retain the foundation's complete operation-selection boundary.
    internal = structural_check(frozen(STRUCTURAL), sources[STRUCTURAL])
    registry_check(sources, internal)
    for path, source in sources.items():
        if path != GENERIC:
            assert not re.search(r'Notation\s+"[^"\n]*≈ₚ', without_comments(source)), 'Competing glyph owner: ' + path
    client_check(sources[CLIENT])
    for path in PROBE_PATHS:
        code = without_comments(sources[path])
        assert code.count('(t ≈ₚ[RR] u) =') == 3
        assert code.count('Proof. reflexivity. Qed.') == 3
        for name in ['weighted_bind_route', 'real_bind_route', 'generic_notation']:
            assert name in code
        old = historical(path)
        restored = re.sub(r'Section PublicBindRoutes\.[\s\S]*?End PublicBindRoutes\.', '', sources[path])
        restored = restored.replace('Fail Definition generic_notation {E A} (t : ptree E MN A) := (t ≈ₚ t).', '')
        restored = restored.replace('(t ≈ₚ[RR] u) =', 'canonical_peutt RR t u =')
        assert tokens(restored) == tokens(old), 'Changed full-profile probe: ' + path
    from audit_architecture import aggregate_check
    aggregate_check()
    print(f'{len(old_paths)} baseline modules: production limited to notation/alias edits; snapshots unchanged.')
    print('Single public glyph owner, four existing routes, independent import orders, public-only client checked.')


def compiled_check():
    paths = sorted(PROBE_PATHS | {CLIENT})
    endpoints = []
    for path in paths:
        module = 'PTree.' + path.removeprefix('theories/').removesuffix('.v').replace('/', '.')
        endpoints += [module + '.' + n for n in re.findall(r'^Example\s+(\w+)', without_comments((ROOT/path).read_text()), re.M)]
    # Behavioral bind already has classical choice dependencies, separately
    # frozen in the 505-entry contract (not the external-domain whitelist).
    # Inherit precisely that old endpoint's assumptions, never a new whitelist.
    manifest = json.loads(historical('docs/CONTRACTS.json'))
    reference = next(e for e in manifest['endpoints'] if e['name'] == 'PTree.Eq.FreeOmega.Bind.peutt_bind')
    allowed = SOUNDNESS_AXIOMS | logical_axioms(reference['assumptions'])
    facade = query(['PTree.API.FreeOmega.peutt_bind'])[0]
    for field in ['type', 'assumptions']:
        assert facade[field] == reference[field], ('Public bind drift', field)
    endpoints += ['PTree.Eq.FreeOmega.Bind.peutt_bind']
    for entry in query(endpoints):
        assert logical_axioms(entry['assumptions']) <= allowed, entry['name']
    print(f'{len(endpoints)} public/client endpoints: only frozen bind + existing backend axioms.')
    print('Public bind type/assumptions exactly match the frozen heterogeneous FreeOmega corollary.')


def kernel_check():
    paths = PROBE_PATHS | {PEUTT, GENERIC, FREEOMEGA, CLIENT, FACADE_TEST, AGGREGATE,
        'theories/API/Behavior.v', 'theories/PTree.v',
        'theories/Regression/Infrastructure/StructuralRegistry.v',
        'theories/Regression/Infrastructure/ArchitectureBoundaries.v'}
    command = ['opam', 'exec', '--', 'coqchk', '-silent', '-R', '_build/default/theories', 'PTree']
    for path in sorted(paths):
        command += ['-norec', 'PTree.' + path.removeprefix('theories/').removesuffix('.v').replace('/', '.')]
    subprocess.run(command, cwd=ROOT, check=True)
    print(f'{len(paths)} safe module bodies kernel-checked jointly (-norec; dependencies trusted; Gate M excluded).')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    parser.add_argument('--kernel', action='store_true')
    args = parser.parse_args()
    source_check()
    if args.compiled:
        compiled_check()
    if args.kernel:
        kernel_check()
