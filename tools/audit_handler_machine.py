#!/usr/bin/env python3
"""Additive arbitrary-handler proof: preserve the frozen operational checkpoint."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = '525a57fc6e79e0e73e7a70ae98e77946af6371c4'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
MODULES = ['Interp/HandlerMachine', 'Interp/HandlerMachineScheduling',
           'Interp/HandlerMachineAcceleration', 'Interp/Unrestricted',
           'Interp/FreeOmega/Unrestricted', 'Regression/Semantics/UnrestrictedInterp']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}
ENDPOINTS = ['PTree.' + module + '.' + name for module, names in {
    'Interp.HandlerMachine': ['handler_config', 'handler_primitive_kernel', 'handler_machine_kernel',
        'handler_machine_kernel_related', 'handler_machine_finite_related', 'handler_machine_complete_related'],
    'Interp.HandlerMachineScheduling': ['handler_primitive_le_tree', 'handler_tree_le_primitive',
        'handler_primitive_hitting_iff'],
    'Interp.HandlerMachineAcceleration': ['finite_head_bind_assoc', 'handler_phase_grid_le_primitive',
        'handler_primitive_le_phase_grid', 'handler_phase_diagonal_hitting_iff',
        'handler_phase_grid_row_lub', 'handler_machine_hitting_sound'],
    'Interp.Unrestricted': ['handler_vis_fusion', 'peutt_interp', 'peutt_interp_Proper'],
    'Interp.FreeOmega.Unrestricted': ['peutt_interp'],
    'Regression.Semantics.UnrestrictedInterp': ['internally_returning_reader',
        'handler_return_is_internal', 'reader_source_enters_handler', 'heterogeneous_elimination',
        'infinitely_many_eliminated_events', 'eliminating_setoid_rewrite',
        'partial_mixed_handler', 'real_arbitrary_handler'],
}.items() for name in names]


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def check_new(sources):
    assert NEW <= set(sources), 'Incomplete handler-machine increment'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
        assert not re.search(r'#\[global\]|Global (?:Instance|Existing)', code), p
        if p.startswith('theories/Interp/') and '/FreeOmega/' not in p:
            assert not re.search(r'FreeOmega|MathComp|OmegaVal|Eq\.Internal|Prob\.Domain', code), p
    acceleration = without_comments(sources['theories/Interp/HandlerMachineAcceleration.v'])
    for name in ['sem_lub_double_diagonal', 'sem_bind_diagonal_lub', 'sem_lub_cofinal',
                 'handler_primitive_le_phase_grid', 'handler_phase_grid_le_primitive']:
        assert name in acceleration, 'Missing finite/limit bridge: ' + name
    final = without_comments(sources['theories/Interp/Unrestricted.v'])
    for name in ['handler_machine_complete_related', 'handler_machine_hitting_sound',
                 'peutt_interp_of_vis_fusion', 'relational_lub FO']:
        assert name in final, 'Missing proof stage: ' + name
    assert 'guarded_handler' not in final, 'Arbitrary-handler result regressed to visible guarding'
    assert re.findall(r'\bVariable (\w+)', final) == ['Hzero', 'Hlimit', 'handler']
    specialization = without_comments(sources['theories/Interp/FreeOmega/Unrestricted.v'])
    assert 'apply (PTree.Interp.Unrestricted.peutt_interp' in specialization
    assert not re.search(r'\b(?:induction|cofix|coinduction)\b', specialization)


def previous_sources(sources):
    from audit_state_preservation import previous_sources as before_state
    sources = before_state(sources)
    if not (NEW & set(sources)):
        return sources
    check_new(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    for line in IMPORTS:
        assert result[ALL].splitlines().count(line) == 1, 'Missing/duplicate import: ' + line
        result[ALL] = result[ALL].replace(line + '\n', '')
    return result


def check_source(sources):
    from audit_state_preservation import previous_sources as before_state
    sources = before_state(sources)
    old = {p for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
           cwd=ROOT, text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW, 'Unapproved theory addition/deletion'
    prior = previous_sources(sources)
    for p in old:
        assert prior[p] == frozen(p), 'Frozen theory changed: ' + p
    lines = sources[ALL].splitlines()
    assert lines[2:] == sorted(set(lines[2:])), 'Unsorted/duplicate aggregate'
    for p in ['docs/CONTRACTS.json', 'docs/MATHCOMP_DIRECT_CONTRACTS.json',
              'docs/EFFECT_EXECUTION_CONTRACTS.json']:
        assert (ROOT/p).read_text() == frozen(p), 'Frozen contract snapshot changed: ' + p
    print(f'{len(old)} existing theory modules unchanged; six additive handler modules.')


def compiled_check():
    snapshot = json.loads((ROOT/'docs/HANDLER_MACHINE_CONTRACTS.json').read_text())
    assert snapshot['baseline'] == BASELINE
    actual = query(ENDPOINTS)
    compare(snapshot['endpoints'], actual)
    for item in actual:
        assert logical_axioms(item['assumptions']) <= SOUNDNESS_AXIOMS, item['name']
        if item['name'].startswith(('PTree.Interp.HandlerMachine', 'PTree.Interp.Unrestricted.')):
            assert not logical_axioms(item['assumptions']), item['name']
            assert not re.search(r'FreeOmega|OmegaVal|MathComp', item['type']), item['name']
    print(f'{len(actual)} compiled contracts; generic machine/preservation proofs are axiom-free.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
