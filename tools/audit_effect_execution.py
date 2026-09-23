#!/usr/bin/env python3
"""Additive State/fold/replay checkpoint; no claim of eliminating peutt fusion."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = '7b4c9714bb3845ed283a68fd084a6b4b33073e6f'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
NEW = {'theories/' + p + '.v' for p in [
    'Core/Fold', 'Interp/State', 'Interp/StateFacts', 'Interp/StateStrong', 'Interp/StateFold',
    'Execution/Runner', 'Execution/Backend/SubEnumQ', 'Examples/StateCounter',
    'Regression/Infrastructure/Execution', 'Regression/Backend/RationalReplay']}
IMPORTS = {'Require PTree.' + p.removeprefix('theories/').removesuffix('.v').replace('/', '.') + '.'
           for p in NEW}
ENDPOINTS = ['PTree.' + module + '.' + name for module, names in {
    'Core.Fold': ['fold_step', 'fold', 'fold_step_vis', 'fold_step_prob'],
    'Interp.State': ['get', 'put', 'run_state', 'state_result_rel', 'observe_run_state'],
    'Interp.StateFacts': ['run_state_ret', 'run_state_tau', 'run_state_prob', 'run_state_get',
                         'run_state_put', 'run_state_forward', 'run_state_pstruct', 'run_state_bind'],
    'Interp.StateStrong': ['run_state_pstrong'],
    'Interp.StateFold': ['state_effect', 'state_sample', 'fold_state', 'state_effect_get',
                        'state_effect_put', 'state_effect_forward', 'state_sample_preserves_state'],
    'Execution.Runner': ['run', 'executes', 'run_sound', 'executes_complete', 'run_finished_iff',
                         'run_finished_more_fuel'],
    'Execution.Backend.SubEnumQ': ['pick_interval_support', 'pick_interval_missing',
                                  'replay_sample_support', 'replay_sample_missing'],
    'Examples.StateCounter': ['tick_state_equation', 'replay_two_attempts_path',
                              'coin_selects_bit', 'coin_bit_expectation', 'counter_replay_contract'],
}.items() for name in names]


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def check_new(sources):
    assert NEW <= set(sources), 'Incomplete effects/execution increment'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Instance|Existing|Hint)\b|Unset .*Checking', code), p
        assert not re.search(r'\b(?:FreeOmega|OmegaVal|MathCompKernelMeasure|peutt)\b',
                             '\n'.join(l for l in code.splitlines() if not l.startswith('Fail Check'))), p
        assert not re.search(r'\b(?:Variant|Inductive)\s+(?:stateE|readerE|writerE|exceptE)', code), p
    runner = without_comments(sources['theories/Execution/Runner.v'])
    for phrase in ['Missing => (Lost, seed\')', 'NoEntropy => (EntropyExhausted, seed\')',
                   'O => (Timeout, seed)', 'finished result ->', 'run_finished_more_fuel']:
        assert phrase in runner, 'Lost/timeout/entropy or operational boundary changed: ' + phrase
    fold = without_comments(sources['theories/Core/Fold.v'])
    assert 'Variable handle : forall X, E X -> T X.' in fold
    assert 'Variable sample : forall X, MN X -> T X.' in fold
    assert 'ProbE' not in fold
    state = without_comments(sources['theories/Interp/State.v'])
    assert 'From ITree.Events Require Import State.' in state
    assert 'CoFixpoint run_state' in state
    assert 'stateE S' in state
    assert 'Theorem run_state_pstrong' in sources['theories/Interp/StateStrong.v']


def previous_sources(sources):
    if not (NEW & set(sources)):
        return sources
    check_new(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    for line in IMPORTS:
        assert result[ALL].splitlines().count(line) == 1, 'Missing/duplicate new import: ' + line
        result[ALL] = result[ALL].replace(line + '\n', '')
    return result


def check_source(sources):
    old = {p for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
           cwd=ROOT, text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW, 'Unapproved addition/deletion'
    previous = previous_sources(sources)
    for p in old:
        assert previous[p] == frozen(p), 'Frozen theory changed: ' + p
    lines = sources[ALL].splitlines()
    assert lines[2:] == sorted(set(lines[2:])), 'Unsorted/duplicate aggregate'
    for p in ['docs/CONTRACTS.json', 'docs/MATHCOMP_DIRECT_CONTRACTS.json']:
        assert (ROOT / p).read_text() == frozen(p), 'Frozen contract snapshot changed: ' + p
    extract = without_comments((ROOT / 'extraction/state-counter/Extract.v.in').read_text())
    assert 'Extraction "counter.ml" counter_replay.' in extract
    assert not re.search(r'Extract (?:Constant|Inductive)|Unset .*Checking|ExtrOcamlNatInt', extract)
    print(f'{len(old)} existing theory modules unchanged; ten additive modules; no new capability/checker bypass.')


def compiled_check():
    snapshot = json.loads((ROOT / 'docs/EFFECT_EXECUTION_CONTRACTS.json').read_text())
    assert snapshot['baseline'] == BASELINE
    results = query(ENDPOINTS, sorted({e.rsplit('.', 1)[0] for e in ENDPOINTS}))
    compare(snapshot['endpoints'], results)
    for e in results:
        assert logical_axioms(e['assumptions']) <= SOUNDNESS_AXIOMS, e['name']
        if not e['name'].startswith('PTree.Interp.StateFacts.run_state_pstruct') and \
           not e['name'].startswith('PTree.Interp.StateStrong.'):
            # Exact operational/interval proofs need no probability axioms.
            assert not logical_axioms(e['assumptions']), e['name']
    print(f'{len(results)} compiled operational/structural contracts; no arbitrary peutt preservation claim.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
