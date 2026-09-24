#!/usr/bin/env python3
"""Additive ITree elaboration: frozen semantics, actual datatype, explicit laws."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = '002f0a6'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
MODULES = ['Core/ITreeBridge', 'Interp/ITreeStructural', 'Interp/ITreeFacts',
           'Interp/FreeOmega/ITreeCompletion', 'Examples/ITreeSampling',
           'Regression/Semantics/ITreeBridge']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def check_new(sources):
    assert NEW <= set(sources), 'Incomplete ITree bridge'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
        assert not re.search(r'#\[global\]|Global (?:Instance|Existing)', code), p
        if p.startswith('theories/Interp/') and '/FreeOmega/' not in p:
            assert not re.search(r'FreeOmega|MathComp|OmegaVal|Prob\.Domain', code), p
    core = without_comments(sources['theories/Core/ITreeBridge.v'])
    for token in ['CoFixpoint from_itree', '(t : itree E A)', 'Prob mu',
                  'Handler.case_ sample_handler Handler.id_', 'PTree.interp h (from_itree t)']:
        assert token in core, 'Missing actual datatype/sampling bridge: ' + token
    assert not re.search(r'Semantic|peutt|Prob\.|Interp\.|Eq\.', core)
    structural = without_comments(sources['theories/Interp/ITreeStructural.v'])
    for token in ['from_itree_bind_candidate', 'from_itree_iter_candidate',
                  'pstruct_interp_bind', 'pstruct_interp_iter', 'pstruct_interp_compose']:
        assert token in structural, 'Missing compositional proof: ' + token
    facts = without_comments(sources['theories/Interp/ITreeFacts.v'])
    for n in ['ret', 'tau', 'event', 'trigger', 'sample', 'vis', 'bind', 'iter',
              'sample_trigger', 'postcompose']:
        assert 'Theorem elab_' + n + ' ' in facts
    thin = without_comments(sources['theories/Interp/FreeOmega/ITreeCompletion.v'])
    assert not re.search(r'\b(?:induction|cofix|coinduction)\b', thin)
    example = sources['theories/Examples/ITreeSampling.v']
    for token in ['two_coins : itree (probE SubEnumQ) bool', 'two_coins_elaborates',
                  'ITree.trigger (Sample fair_coin)', 'retry_elaborates']:
        assert token in example
    reg = sources['theories/Regression/Semantics/ITreeBridge.v']
    for token in ['Constraint Set < hi', 'partial_sampling_not_normalized',
                  'ordinary_event_retained', 'Fail Check PTree.Eq.PEutt.peutt.']:
        assert token in reg


def previous_sources(sources):
    from audit_effect_algebra import previous_sources as previous_algebra
    sources = previous_algebra(sources)
    if not (NEW & set(sources)):
        return sources
    check_new(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    for line in IMPORTS:
        assert result[ALL].splitlines().count(line) == 1, 'Missing/duplicate import: ' + line
        result[ALL] = result[ALL].replace(line + '\n', '')
    return result


def check_source(sources):
    from audit_effect_algebra import previous_sources as previous_algebra
    sources = previous_algebra(sources)
    old = {p for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
               cwd=ROOT, text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW, 'Unapproved theory addition/deletion'
    prior = previous_sources(sources)
    for p in old:
        assert prior[p] == frozen(p), 'Frozen theory changed: ' + p
    lines = sources[ALL].splitlines()
    assert lines[2:] == sorted(set(lines[2:])), 'Unsorted/duplicate aggregate'
    print(f'{len(old)} old theory modules conserved byte-for-byte; six additive bridge modules.')


def compiled_check():
    data = json.loads((ROOT/'docs/ITREE_BRIDGE_CONTRACTS.json').read_text())
    assert data['baseline'] == BASELINE
    actual = query([e['name'] for e in data['endpoints']])
    compare(data['endpoints'], actual)
    for item in actual:
        axioms = logical_axioms(item['assumptions'])
        assert axioms <= SOUNDNESS_AXIOMS, item['name']
        if item['name'].startswith('PTree.Core.ITreeBridge.'):
            assert not axioms, item['name']
        if item['name'].startswith('PTree.Interp.ITreeFacts.'):
            assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal', item['type']), item['name']
    print(f'{len(actual)} compiled bridge contracts; existing logical-axiom whitelist preserved.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
