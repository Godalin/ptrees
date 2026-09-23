#!/usr/bin/env python3
"""Operation routing gate, before the separate public-notation migration.

No snapshot regeneration: replay the frozen structural/basic definitions and
compare elaborated signatures/assumptions to the current compiled constants.
"""
import argparse
import re
import subprocess
from pathlib import Path
from audit_assumptions import ROOT, without_comments, query, logical_axioms, SOUNDNESS_AXIOMS
from audit_rational_positions import endpoint_query

BASELINE = '04475b2'
STRUCTURAL = 'theories/Prob/FreeOmega/StructuralMeasure.v'
REGISTRY = {
    'theories/API/EnumQ.v': 'EnumQ_CanonicalBehavior',
    'theories/API/SubEnumQ.v': 'SubEnumQ_CanonicalBehavior',
    'theories/API/SubEnumR.v': 'SubEnumR_CanonicalBehavior',
    'theories/Eq/Backend/MathComp/Direct.v': 'MathComp_CanonicalBehavior',
}
PROBES = ['CanonicalBehavior', 'CanonicalBehaviorStructuralFirst',
          'CanonicalBehaviorNativeFirst', 'StructuralRegistry']
NEW = {'theories/API/' + n + '.v' for n in ['Behavior', 'BehaviorFreeOmega', 'SubEnumR']}
NEW |= {'theories/Regression/Infrastructure/' + n + '.v' for n in PROBES}
LOCALS = {
    'theories/Examples/BernoulliFactory/OperationalVonNeumann.v': [
        'FreeOmegaSemanticMeasure', 'FreeOmegaSemanticOmega'],
    'theories/Examples/BernoulliFactory/OperationalRationalBernoulli.v': [
        'FreeOmegaSemanticMeasure', 'FreeOmegaSemanticOmega'],
    'theories/Examples/InteractiveVonNeumann/InteractiveVonNeumannService.v': [
        'FreeOmegaSemanticMeasure', 'FreeOmegaSemanticOmega'],
    'theories/Interp/FreeOmega/Cofinality.v': [
        'FreeOmegaSemanticMeasure', 'FreeOmegaSemanticOmega'],
    'theories/Eq/FreeOmega/Bind.v': [
        'FreeOmegaSemanticMeasure', 'FreeOmegaSemanticOmega'],
    'theories/Interp/FreeOmega/Translate.v': [
        'FreeOmegaSemanticMeasure', 'FreeOmegaSemanticOmega'],
    'theories/Eq/FreeOmega/Base.v': [
        'FreeOmegaSemanticMeasure', 'FreeOmegaSemanticOmega'],
    'theories/Eq/FreeOmega/Relation.v': [
        'FreeOmegaSemanticMeasure', 'FreeOmegaSemanticOmega'],
    'theories/Eq/Internal/FreeOmega/FiniteInternalJoint.v': [
        'FreeOmegaSemanticMeasureCoreLaws', 'FreeOmegaSemanticMeasureCouplingAELaws'],
    'theories/Examples/BernoulliFactory/OperationalBernoulliFactory.v': [
        'FreeOmegaSemanticMeasure', 'FreeOmegaSemanticOmega'],
}


def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def tokens(text):
    return ' '.join(without_comments(text).split())


def structural_family(source):
    return re.findall(r'^#\[global\] Polymorphic Instance (\w+)', without_comments(source), re.M)


def structural_check(old, new):
    family = structural_family(old)
    assert len(family) == 11 and 'FreeOmegaMixedMeasure' in family
    expected = old
    for name in family:
        if name != 'FreeOmegaMixedMeasure':
            expected = expected.replace('#[global] Polymorphic Instance ' + name,
                                        '#[local] Polymorphic Instance ' + name)
    assert tokens(new) == tokens(expected), 'Structural definition/proof changed beyond registration'
    return set(family) - {'FreeOmegaMixedMeasure'}


def registry_check(sources, internal):
    found = {}
    for path, source in sources.items():
        code = without_comments(source)
        # Declarations and later registrations must both be accounted for.
        for name in internal:
            for match in re.finditer(r'(?m)^([^\n]*\b(?:Instance|Instances)\s+[^\n]*\b'
                                     + name + r'\b[^\n]*)', code):
                assert '#[local]' in match[0], 'Exported structural registration: ' + path
        for match in re.finditer(r'(?m)^(?:#\[\w+\]\s+)?(?:Polymorphic\s+)?Instance\s+(\w+)'
                                 r'[\s\S]*?\.(?=\s|$)', code):
            if not re.search(r'\bCanonicalBehavior\b', match[0]):
                continue
            assert match[0].startswith('#[global]'), 'Unreviewed route registration: ' + path
            assert path not in found, 'Duplicate route: ' + path
            found[path] = match[1]
        for name in REGISTRY.values():
            assert not re.search(r'\bExisting\s+Instances?\s+[^.]*\b' + name + r'\b', code), \
                'Route re-registration: ' + path
    assert found == REGISTRY, ('Canonical registry drift', found)
    behavior = without_comments(sources['theories/API/Behavior.v'])
    block = behavior.split('Class CanonicalBehavior', 1)[1].split('}.', 1)[0]
    assert re.findall(r'\b(behavior_\w+)\s*:', block) == [
        'behavior_frontier', 'behavior_measure', 'behavior_mixed', 'behavior_omega']
    assert not re.search(r'Laws|:>|::|admissible|modelable', block), 'Selector bundles laws/coercions'
    assert not re.search(r'Existing\s+Instances?\s+behavior_', behavior)


def source_check():
    sources = {p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')}
    paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
                                    cwd=ROOT, text=True).splitlines()
    old_paths = {p for p in paths if p.endswith('.v')}
    assert set(sources) == old_paths | NEW, 'Unreviewed theory module addition/deletion'
    internal = structural_check(frozen(STRUCTURAL), sources[STRUCTURAL])
    registry_check(sources, internal)
    allowed = set(REGISTRY) | set(LOCALS) | {STRUCTURAL,
        'theories/Eq/PTreeKernel.v', 'theories/Eq/PEutt.v',
        'theories/Regression/Backend/MathCompDirect.v',
        'theories/Regression/Infrastructure/AllImports.v'}
    for path in old_paths - allowed:
        assert sources[path] == frozen(path), 'Unapproved theory/proof change: ' + path
    for path, names in LOCALS.items():
        restored = sources[path]
        for name in names:
            command = '#[local] Existing Instance ' + name + '.'
            assert restored.count(command) == 1
            restored = restored.replace(command, '')
        assert tokens(restored) == tokens(frozen(path)), 'Internal client proof drift: ' + path
    peutt = 'theories/Eq/PEutt.v'
    old = frozen(peutt)
    before, after = old.split('Section PEutt.', 1)
    after = after.replace('  `{NI : SemanticMeasure MN}\n', '', 1)
    assert sources[peutt] == before + 'Section PEutt.' + after
    kernel = 'theories/Eq/PTreeKernel.v'
    old = frozen(kernel).replace('  `{NI : SemanticMeasure MN}\n', '', 1)
    old = old.replace('  `{MX : MixedMeasure MN MF}\n  `{FO : @SemanticOmega MF FI}.',
                      '  `{MX : MixedMeasure MN MF}.', 1)
    old = old.replace('Definition ptree_stable_target_approx',
                      'Context `{FO : @SemanticOmega MF FI}.\nDefinition ptree_stable_target_approx', 1)
    assert tokens(sources[kernel]) == tokens(old), 'Kernel proof/signature drift'
    # Existing user operations and direct endpoints must survive intact.
    for path in set(REGISTRY) - NEW:
        restored = sources[path]
        name = REGISTRY[path]
        restored, n = re.subn(r'^#\[global\] (?:Polymorphic )?Instance ' + name
                              + r'\b[\s\S]*?\.(?=\n)', '', restored, count=1, flags=re.M)
        assert n == 1
        restored = re.sub(r'^From PTree.API Require Import Behavior(?: BehaviorFreeOmega)?\.\n',
                          '', restored, flags=re.M)
        if path.endswith('/EnumQ.v'):
            restored = restored.replace('From PTree.Prob.Backend.EnumQ Require Import Measure.\n', '')
        assert tokens(restored) == tokens(frozen(path)), 'Existing API/direct endpoint drift: ' + path
    path = 'theories/Regression/Backend/MathCompDirect.v'
    restored = sources[path].replace('From PTree.API Require Import Behavior.\n', '')
    restored, n = re.subn(r'Example direct_canonical_profile\b[\s\S]*?Proof\. reflexivity\. Qed\.',
                          '', restored, count=1)
    assert n == 1 and tokens(restored) == tokens(frozen(path)), 'Existing Gate M regression drift'
    print('Routing source gate: 10 local structural instances, shared mixed operation, '
          '4 concrete selectors; old theory bodies and public notation unchanged.')


def declarations(source):
    return re.findall(r'^(?:#\[\w+\]\s+)?(?:Polymorphic\s+)?'
                      r'(?:Definition|Lemma|Theorem|Instance)\s+(\w+)', without_comments(source), re.M)


def printed_bodies(source, names):
    commands = [source, 'Set Printing All. Set Printing Width 100. Set Printing Depth 100000.']
    for i, name in enumerate(names):
        commands += [f'Goal True. idtac "BODY_{i}". Abort.', 'Print ' + name + '.',
                     f'Goal True. idtac "BODY_END_{i}". Abort.']
    result = subprocess.run(['opam', 'exec', '--', 'coqtop', '-quiet', '-R',
                             '_build/default/theories', 'PTree'], cwd=ROOT,
                            input='\n'.join(commands) + '\n', text=True, capture_output=True)
    assert result.returncode == 0 and not re.search(r'\bError:', result.stdout + result.stderr), \
        result.stderr
    bodies = []
    for i in range(len(names)):
        matches = re.findall(rf'^BODY_{i}\n(.*?)^BODY_END_{i}\n', result.stdout, re.S | re.M)
        assert len(matches) == 1 and matches[0].strip(), 'Missing/duplicate printed body'
        body = re.sub(r'^Fetching opaque proofs[^\n]*\n', '', matches[0], flags=re.M)
        bodies.append(body)
    return bodies


def compiled_check():
    count = 0
    for path, end in [(STRUCTURAL, None), ('theories/Eq/PTreeKernel.v', 'End PTreeKernel.'),
                      ('theories/Eq/PEutt.v', 'End PEutt.')]:
        source = frozen(path)
        if end:
            source = source.split(end, 1)[0] + end + '\n'
        names = declarations(source)
        module = 'PTree.' + path.removeprefix('theories/').removesuffix('.v').replace('/', '.')
        endpoints = [module + '.' + n for n in names]
        current = endpoint_query('Require ' + module + '.', endpoints, endpoints)
        reference = endpoint_query('Module RoutingBaseline.\n' + source + '\nEnd RoutingBaseline.',
                                   endpoints, ['RoutingBaseline.' + n for n in names])
        short = Path(path).stem + '.'
        for a, b in zip(reference, current):
            for field in ['type', 'assumptions']:
                norm = lambda x: ' '.join(x.replace('RoutingBaseline.', short).split())
                assert norm(a[field]) == norm(b[field]), (a['name'], field, a[field], b[field])
        if path == STRUCTURAL:
            actual = printed_bodies('Require ' + module + '.', endpoints)
            historical = printed_bodies('Module RoutingBaseline.\n' + source + '\nEnd RoutingBaseline.',
                                        ['RoutingBaseline.' + n for n in names])
            for name, a, b in zip(names, historical, actual):
                assert norm(a) == norm(b), 'Structural compiled body drift: ' + name
            print(f'{len(names)} structural compiled bodies also agree with frozen replay.')
        count += len(names)
    print(f'{count} replayed structural/basic declarations: compiled types and assumptions preserved.')
    endpoints = []
    for path in NEW:
        module = 'PTree.' + path.removeprefix('theories/').removesuffix('.v').replace('/', '.')
        endpoints += [module + '.' + n for n in re.findall(
            r'^(?:#\[global\]\s+)?(?:Definition|Example|Instance)\s+(\w+)',
            without_comments((ROOT/path).read_text()), re.M)]
    for path, name in REGISTRY.items():
        if '/MathComp/' not in path:
            name = 'PTree.' + path.removeprefix('theories/').removesuffix('.v').replace('/', '.') + '.' + name
            if name not in endpoints:
                endpoints.append(name)
    for entry in query(sorted(endpoints)):
        assert logical_axioms(entry['assumptions']) <= SOUNDNESS_AXIOMS, entry['name']
    print(f'{len(endpoints)} new safe routing definitions/probes respect the existing axiom whitelist.')


def kernel_check():
    paths = set(LOCALS) | NEW | {STRUCTURAL, 'theories/Eq/PTreeKernel.v',
        'theories/Eq/PEutt.v', 'theories/API/EnumQ.v', 'theories/API/SubEnumQ.v',
        'theories/Regression/Infrastructure/AllImports.v'}
    modules = ['PTree.' + p.removeprefix('theories/').removesuffix('.v').replace('/', '.')
               for p in sorted(paths)]
    command = ['opam', 'exec', '--', 'coqchk', '-silent', '-R', '_build/default/theories', 'PTree']
    for module in modules:
        command += ['-norec', module]
    subprocess.run(command, cwd=ROOT, check=True)
    print(f'{len(modules)} safe module bodies kernel-checked jointly; '
          'dependencies not recursively rechecked; Gate M excluded.')


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
