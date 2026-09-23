#!/usr/bin/env python3
"""StateT/fold commutation: explicit algebraic law and a checked target model."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = '1cca4ca'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
MODULES = ['Core/IterationLaws', 'Interp/StateFoldFacts', 'Execution/ITreeFold',
           'Regression/Semantics/StateFold']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}
ENDPOINTS = ['PTree.' + module + '.' + name for module, names in {
    'Core.IterationLaws': ['iteration_map', 'iteration_uniform'],
    'Interp.StateFoldFacts': ['fold_state_as_iter', 'state_fold_square', 'fold_run_state'],
    'Execution.ITreeFold': ['itree_iteration_uniform', 'itree_fold_unfold', 'itree_fold_ret',
                          'itree_fold_tau', 'itree_fold_vis', 'itree_fold_prob'],
    'Regression.Semantics.StateFold': ['state_fold_commutes', 'sample_keeps_separate_algebra',
        'state_get_fold', 'unbounded_counter_fold_agrees', 'bare_iterator_is_not_uniform'],
}.items() for name in names]


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def check_new(sources):
    assert NEW <= set(sources), 'Incomplete State/fold increment'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
        if not p.startswith('theories/Regression/'):
            assert not re.search(r'FreeOmega|MathComp|OmegaVal|SemanticMeasure|sem_lift|peutt', code), p
    law = without_comments(sources['theories/Core/IterationLaws.v'])
    assert not re.search(r'ptree|fold|stateE|Instance', law), 'Uniformity must be an independent explicit law'
    proof = without_comments(sources['theories/Interp/StateFoldFacts.v'])
    assert '(Hunif : @iteration_uniform T MT IT QT)' in proof
    assert 'apply state_fold_square.' in proof
    model = without_comments(sources['theories/Execution/ITreeFold.v'])
    assert 'eutt_iter\'' in model, 'Must prove the target law, not assume it'
    reg = without_comments(sources['theories/Regression/Semantics/StateFold.v'])
    assert '~ @iteration_uniform option option_ops nonuniform_iter option_observation' in reg


def previous_sources(sources):
    if not (NEW & set(sources)):
        return sources
    check_new(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    for line in IMPORTS:
        assert result[ALL].splitlines().count(line) == 1, 'Missing/duplicate import: ' + line
        result[ALL] = result[ALL].replace(line + '\n', '')
    return result


def check_source(sources):
    old = {p for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
           cwd=ROOT, text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW, 'Unapproved theory addition/deletion'
    prior = previous_sources(sources)
    for p in old:
        assert prior[p] == frozen(p), 'Frozen theory changed: ' + p
    lines = sources[ALL].splitlines()
    assert lines[2:] == sorted(set(lines[2:])), 'Unsorted/duplicate aggregate'
    for p in ['docs/CONTRACTS.json', 'docs/MATHCOMP_DIRECT_CONTRACTS.json',
              'docs/EFFECT_EXECUTION_CONTRACTS.json', 'docs/HANDLER_MACHINE_CONTRACTS.json',
              'docs/STATE_PRESERVATION_CONTRACTS.json', 'docs/STANDARD_EFFECTS_CONTRACTS.json']:
        assert (ROOT/p).read_text() == frozen(p), 'Frozen snapshot changed: ' + p
    print(f'{len(old)} prior theory modules unchanged; four additive fold-law modules.')


def compiled_check():
    snapshot = json.loads((ROOT/'docs/STATE_FOLD_CONTRACTS.json').read_text())
    assert snapshot['baseline'] == BASELINE
    actual = query(ENDPOINTS)
    compare(snapshot['endpoints'], actual)
    for item in actual:
        assert logical_axioms(item['assumptions']) <= SOUNDNESS_AXIOMS, item['name']
        if item['name'].startswith(('PTree.Core.', 'PTree.Interp.')):
            assert not logical_axioms(item['assumptions']), item['name']
        if item['name'] == 'PTree.Interp.StateFoldFacts.fold_run_state':
            assert 'iteration_uniform' in item['type']
            assert not re.search(r'FreeOmega|MathComp|OmegaVal|SemanticMeasure', item['type'])
    print(f'{len(actual)} compiled contracts; no probability assumptions or new axioms.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
