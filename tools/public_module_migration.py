"""Explicit, frozen-source relocation ledger for 33cb5d8 public modules.

This is audit data, not a Rocq compatibility layer. No current compiler output
is used to manufacture the expected contracts.
"""
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, without_comments

BASELINE = '33cb5d8'
MOVES = {
    'API/Behavior': 'Eq/Canonical',
    'API/BehaviorFreeOmega': 'Eq/FreeOmega/Canonical',
    'API/EnumQ': 'Eq/Backend/EnumQ',
    'API/SubEnumQ': 'Eq/Backend/SubEnumQ',
    'API/SubEnumR': 'Eq/Backend/SubEnumR',
}
REMOVED = {f'PTree.API.{module}.{name}' for module, names in {
    'EnumQ': ['meas', 'kernel', 'sampleE', 'handle_sample'],
    'SubEnumQ': ['submeas', 'subkernel', 'subSampleE', 'handle_subsample'],
    'Weighted': ['stuckE', 'stuckM'],
}.items() for name in names}


@lru_cache(maxsize=None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


@lru_cache(maxsize=1)
def aliases():
    result = {}
    owners = {'PTreeDefinition': 'Core.PTreeDefinition',
              **{n: 'Eq.' + n for n in ['WellFormedness', 'UnifiedFrontier',
                 'PrimitiveStableHitting', 'PStruct', 'PStrong', 'PEutt',
                 'StableHittingComputation', 'ProbabilisticTrace']},
              **{n: 'Eq.FreeOmega.' + n for n in ['Bind', 'Algebra', 'Iter']},
              **{n: 'Interp.FreeOmega.' + n for n in ['Guarded', 'Atomic', 'MDP']}}
    for module in ['Generic', 'FreeOmega', 'SubEnumQ']:
        source = without_comments(frozen('theories/API/' + module + '.v'))
        for name, target in re.findall(r'Notation (\w+)\s*:=\s*([\w.]+)\.', source):
            if not target.startswith('PTree.'):
                owner, suffix = target.split('.', 1)
                target = 'PTree.' + owners[owner] + '.' + suffix
            result['PTree.API.' + module + '.' + name] = target
    return result


def endpoint(name):
    if name in REMOVED:
        return None
    name = aliases().get(name, name)
    for old, new in MOVES.items():
        name = name.replace('PTree.' + old.replace('/', '.') + '.',
                            'PTree.' + new.replace('/', '.') + '.')
    return re.sub(r'\bPEutt\.peutt_bind\b', 'PEutt.peutt_bind_cofinal', name)


def text_relocation(text):
    for old, new in MOVES.items():
        text = text.replace('PTree.' + old.replace('/', '.') + '.',
                            'PTree.' + new.replace('/', '.') + '.')
    text = re.sub(r'\bPEutt\.peutt_bind\b', 'PEutt.peutt_bind_cofinal', text)
    text = re.sub(r'\b(?:BehaviorFreeOmega|Behavior)\.(?=[A-Za-z_])', 'Canonical.', text)
    # Removing API.SubEnumQ removes this printing ambiguity. The fully
    # qualified endpoint still resolves to Interp.Backend.SubEnumQ.
    text = text.replace('@Backend.SubEnumQ.subenumQ_mdp_state_interp_atomic',
                        '@SubEnumQ.subenumQ_mdp_state_interp_atomic')
    return text


def expected_contracts():
    old = json.loads(frozen('docs/CONTRACTS.json'))
    entries = {}
    for entry in old['endpoints']:
        name = endpoint(entry['name'])
        if name is None:
            continue
        new = dict(entry, name=name,
                   type=text_relocation(entry['type']),
                   assumptions=text_relocation(entry['assumptions']))
        if name in entries:
            assert entries[name] == new, 'Conflicting old contracts for one owner: ' + name
        entries[name] = new
    result = {key: sorted({endpoint(n) for n in old[key]} - {None})
              for key in ['api', 'capability', 'soundness']}
    def file_owner(name):
        parts = name.split('.')[1:-1]
        while parts and not (ROOT/'theories'/('/'.join(parts) + '.v')).is_file():
            parts.pop()
        assert parts, 'No source owner: ' + name
        return 'PTree.' + '.'.join(parts)
    result['modules'] = sorted({file_owner(n) for n in entries})
    result['endpoints'] = [entries[n] for n in sorted(entries)]
    assert len(old['endpoints']) == 505
    return result


def expected_mathcomp():
    old = json.loads(frozen('docs/MATHCOMP_DIRECT_CONTRACTS.json'))
    def walk(value):
        if isinstance(value, str):
            return text_relocation(value)
        if isinstance(value, list):
            return [walk(x) for x in value]
        if isinstance(value, dict):
            return {k: walk(v) for k, v in value.items()}
        return value
    return walk(old)


def registry_check(sources, internal):
    # Reuse the accepted four-field/no-blanket/structural-registry check after
    # inverse namespace relocation. Mathematical declarations are unchanged.
    from audit_behavior_routing import registry_check as foundation_registry
    inverse = {'theories/' + v + '.v': 'theories/' + k + '.v' for k, v in MOVES.items()}
    foundation_registry({inverse.get(p, p): s for p, s in sources.items()}, internal)


REGISTRY = {'theories/' + MOVES['API/' + n] + '.v': n + '_CanonicalBehavior'
            for n in ['EnumQ', 'SubEnumQ', 'SubEnumR']}
REGISTRY['theories/Eq/Backend/MathComp/Direct.v'] = 'MathComp_CanonicalBehavior'
