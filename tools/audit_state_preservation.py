#!/usr/bin/env python3
"""State-indexed follow-up: no changes to fixed-handler or backend proofs."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = 'c2c047f'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
MODULES = ['Interp/StateMachine', 'Interp/StateMachineScheduling', 'Interp/StatePreservation',
           'Interp/FreeOmega/State', 'Regression/Semantics/StatePreservation']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}
ENDPOINTS = ['PTree.' + module + '.' + name for module, names in {
    'Interp.StateMachine': ['state_config', 'state_head_result', 'state_primitive_kernel',
        'state_machine_kernel', 'state_config_rel', 'state_machine_kernel_related', 'state_machine_complete_related'],
    'Interp.StateMachineScheduling': ['state_primitive_tree_approx', 'state_phase_grid_le_primitive',
        'state_primitive_le_phase_split', 'state_phase_grid_row_lub', 'state_machine_hitting_sound'],
    'Interp.StatePreservation': ['run_state_peutt', 'run_state_peutt_Proper',
        'run_state_peutt_eq', 'run_state_peutt_eq_Proper'],
    'Interp.FreeOmega.State': ['run_state_peutt', 'run_state_peutt_eq'],
    'Regression.Semantics.StatePreservation': ['weak_source_preserved', 'actual_state_setoid_rewrite',
        'get_is_eliminated', 'put_is_eliminated', 'state_bind_algebra', 'state_iter_algebra',
        'heterogeneous_state_result', 'retry_source_weak_rewrite', 'state_update_is_not_reordered',
        'real_state_preservation'],
}.items() for name in names]


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def check_new(sources):
    assert NEW <= set(sources), 'Incomplete State preservation increment'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
        assert not re.search(r'#\[global\]|Global (?:Instance|Existing)', code), p
        if p.startswith('theories/Interp/') and '/FreeOmega/' not in p:
            assert not re.search(r'FreeOmega|MathComp|OmegaVal|Eq\.Internal|Prob\.Domain', code), p
    final = without_comments(sources['theories/Interp/StatePreservation.v'])
    assert re.findall(r'\bVariable (\w+)', final) == ['Hbind', 'Hzero', 'Hlimit']
    for name in ['peutt_coinduction', 'state_machine_hitting_sound', 'state_machine_complete_related',
                 'state_result_rel RR', 'eq ==>']:
        assert name in final, name
    assert not re.search(r'\bpstruct\b|\bpstrong\b|guarded_handler', final)
    schedule = without_comments(sources['theories/Interp/StateMachineScheduling.v'])
    for name in ['finite_head_bind_assoc', 'HandlerMachineAcceleration.target_kernel_lub',
                 'sem_lub_double_diagonal', 'sem_lub_cofinal', 'state_primitive_tree_approx']:
        assert name in schedule, name
    specialization = without_comments(sources['theories/Interp/FreeOmega/State.v'])
    assert 'apply (StatePreservation.run_state_peutt ' in specialization
    assert not re.search(r'\b(?:induction|cofix|coinduction)\b', specialization)


def previous_sources(sources):
    from audit_standard_effects import previous_sources as before_effects
    sources = before_effects(sources)
    if not (NEW & set(sources)):
        return sources
    check_new(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    for line in IMPORTS:
        assert result[ALL].splitlines().count(line) == 1, 'Missing/duplicate import: ' + line
        result[ALL] = result[ALL].replace(line + '\n', '')
    return result


def check_source(sources):
    from audit_standard_effects import previous_sources as before_effects
    sources = before_effects(sources)
    old = {p for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
           cwd=ROOT, text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW, 'Unapproved theory addition/deletion'
    prior = previous_sources(sources)
    for p in old:
        assert prior[p] == frozen(p), 'Frozen theory changed: ' + p
    lines = sources[ALL].splitlines()
    assert lines[2:] == sorted(set(lines[2:])), 'Unsorted/duplicate aggregate'
    for p in ['docs/CONTRACTS.json', 'docs/MATHCOMP_DIRECT_CONTRACTS.json',
              'docs/EFFECT_EXECUTION_CONTRACTS.json', 'docs/HANDLER_MACHINE_CONTRACTS.json']:
        assert (ROOT/p).read_text() == frozen(p), 'Frozen contract snapshot changed: ' + p
    print(f'{len(old)} existing theory modules unchanged; five additive State modules.')


def compiled_check():
    snapshot = json.loads((ROOT/'docs/STATE_PRESERVATION_CONTRACTS.json').read_text())
    assert snapshot['baseline'] == BASELINE
    actual = query(ENDPOINTS)
    compare(snapshot['endpoints'], actual)
    for item in actual:
        assert logical_axioms(item['assumptions']) <= SOUNDNESS_AXIOMS, item['name']
        if item['name'].startswith(('PTree.Interp.StateMachine', 'PTree.Interp.StatePreservation.')):
            assert not logical_axioms(item['assumptions']), item['name']
            assert not re.search(r'FreeOmega|OmegaVal|MathComp', item['type']), item['name']
    print(f'{len(actual)} compiled contracts; generic State proof is axiom-free.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
