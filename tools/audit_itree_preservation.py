#!/usr/bin/env python3
"""Additive source-eutt and source-interp gate; frozen semantics and signatures."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = 'd79caca'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
MODULES = ['Interp/ITreeEutt', 'Interp/ITreeSourceInterp', 'Interp/ITreePreservation',
           'Interp/FreeOmega/ITreePreservation', 'Regression/Semantics/ITreePreservation']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def check_new(sources):
    assert NEW <= set(sources), 'Incomplete source-ITree increment'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
        assert not re.search(r'#\[global\]|Global (?:Instance|Existing)', code), p
        if '/FreeOmega/' not in p and '/Regression/' not in p:
            assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal|Backend', code), p
    base = without_comments(sources['theories/Interp/ITreeEutt.v'])
    for token in ['from_itree_eutt', 'eutt RR t u', 'peutt_coinduction',
                  'from_itree_no_head_hitting', 'classic', 'stable_hitting_match_of_hitting_lift']:
        assert token in base, token
    assert 'Variable Hlimit' not in base and 'relational_lub' not in base
    square = without_comments(sources['theories/Interp/ITreeSourceInterp.v'])
    for token in ['itree_interp_before_eutt', 'Interp.interp h t',
                  'from_itree_interp_before', 'PTree.interp lifted_handler', 'evis', 'etau']:
        assert token in square, token
    api = without_comments(sources['theories/Interp/ITreePreservation.v'])
    for token in ['from_itree_interp', 'interp_itree_eutt', 'elaborate_eutt',
                  'elaborate_closed_eutt', 'interp_itree_source_interp',
                  'elaborate_source_interp', 'elaborate_eutt_Proper',
                  'Unrestricted.peutt_interp', 'Interp.interp h t']:
        assert token in api, token
    assert 'guarded_handler' not in api
    reg = sources['theories/Regression/Semantics/ITreePreservation.v']
    for token in ['embedded_heterogeneous_return', 'embedded_infinite_service',
                  'divergence_has_no_head', 'source_divergence_not_return',
                  'returning_source_square', 'divergent_source_square',
                  'two_query_source_square', 'sampling_source_square',
                  'lowering_partial_source_equation', 'real_lowering_eutt',
                  'Constraint Set < high', 'setoid_rewrite H']:
        assert token in reg, token


def previous_sources(sources):
    from audit_eventful_iteration import previous_sources as before_iteration
    sources = before_iteration(sources)
    if not (NEW & set(sources)):
        return sources
    check_new(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    for line in IMPORTS:
        assert result[ALL].splitlines().count(line) == 1, 'Missing/duplicate import: ' + line
        result[ALL] = result[ALL].replace(line + '\n', '')
    return result


def check_source(sources):
    from audit_eventful_iteration import previous_sources as before_iteration
    sources = before_iteration(sources)
    old = {p for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
               cwd=ROOT, text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW, 'Unapproved theory addition/deletion'
    prior = previous_sources(sources)
    for p in old:
        assert prior[p] == frozen(p), 'Frozen theory changed: ' + p
    lines = sources[ALL].splitlines()
    assert lines[2:] == sorted(set(lines[2:])), 'Unsorted/duplicate aggregate'
    print(f'{len(old)} old theory modules conserved; five additive source-ITree modules.')


def compiled_check():
    data = json.loads((ROOT/'docs/ITREE_PRESERVATION_CONTRACTS.json').read_text())
    assert data['baseline'] == BASELINE
    actual = query([e['name'] for e in data['endpoints']])
    compare(data['endpoints'], actual)
    for item in actual:
        assert logical_axioms(item['assumptions']) <= SOUNDNESS_AXIOMS, item['name']
        if item['name'].startswith(('PTree.Interp.ITreeEutt.', 'PTree.Interp.ITreeSourceInterp.',
                                    'PTree.Interp.ITreePreservation.')):
            assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal|Backend', item['type']), item['name']
        if item['name'] == 'PTree.Interp.ITreeEutt.from_itree_eutt':
            assert logical_axioms(item['assumptions']) == {'Classical_Prop.classic'}
            for forbidden in ['relational_lub', 'SemanticMeasure MN', 'SemanticMeasureOrderLaws',
                              'Diagonal', 'Fubini', 'guarded_handler']:
                assert forbidden not in item['type'], forbidden
        if item['name'].startswith('PTree.Interp.ITreeSourceInterp.'):
            assert not logical_axioms(item['assumptions']), item['name']
    print(f'{len(actual)} compiled source-ITree contracts; classical head split explicit, no new axiom whitelist.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
