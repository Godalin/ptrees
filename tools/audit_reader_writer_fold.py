#!/usr/bin/env python3
"""Lawful ReaderT/WriterT with actual ITree commuting; no universal target claim."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, without_comments

BASELINE = '2d59640'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
MODULES = ['Core/ReaderT', 'Core/WriterT', 'Interp/FoldITree',
           'Interp/ReaderFold', 'Interp/ReaderFoldITree', 'Interp/WriterFold',
           'Interp/WriterFoldFacts', 'Interp/WriterFoldITree',
           'Regression/Semantics/ReaderWriterFold']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def check_new(sources):
    assert NEW <= set(sources), 'Incomplete Reader/Writer increment'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
        assert not re.search(r'#\[global\]|Global (?:Instance|Existing)', code), p
        if '/Regression/' not in p:
            assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal|SemanticMeasure|Prob\.', code), p
    for owner in ['Reader', 'Writer']:
        core = without_comments(sources[f'theories/Core/{owner}T.v'])
        for token in [owner.lower() + 'T_monad_laws', owner.lower() + 'T_iteration_uniform',
                      '(Hunif : @iteration_uniform T MT IT QT)']:
            assert token in core, token
        assert not re.search(r'\b(?:Inductive|CoInductive|Fixpoint|CoFixpoint)\b', core)
        target = without_comments(sources[f'theories/Interp/{owner}FoldITree.v'])
        for token in ['itree_fold_run_' + owner.lower(), 'itree_' + owner.lower() + '_fold_bind',
                      '-> itree F X', 'tau_euttge']:
            assert token in target, token
    writer = without_comments(sources['theories/Core/WriterT.v'])
    for token in ['Monads.writerT', 'MonoidLaws op', 'monoid_plus op (fst wi) (fst wv)']:
        assert token in writer, token
    assert 'Commutative' not in writer
    reg = sources['theories/Regression/Semantics/ReaderWriterFold.v']
    for token in ['writer_bind_keeps_order', 'logs_not_commutative', 'Constraint Set < high',
                  'CoFixpoint reader_service', 'CoFixpoint writer_service', 'itree_iteration_uniform',
                  'writer_sampling_does_not_log', 'Fail Check PTree.Eq.PEutt.peutt.']:
        assert token in reg, token


def previous_sources(sources):
    from audit_itree_preservation import previous_sources as before_itree_preservation
    sources = before_itree_preservation(sources)
    if not (NEW & set(sources)):
        return sources
    check_new(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    for line in IMPORTS:
        assert result[ALL].splitlines().count(line) == 1, 'Missing/duplicate import: ' + line
        result[ALL] = result[ALL].replace(line + '\n', '')
    return result


def check_source(sources):
    from audit_itree_preservation import previous_sources as before_itree_preservation
    sources = before_itree_preservation(sources)
    old = {p for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
               cwd=ROOT, text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW, 'Unapproved theory addition/deletion'
    prior = previous_sources(sources)
    for p in old:
        assert prior[p] == frozen(p), 'Frozen theory changed: ' + p
    lines = sources[ALL].splitlines()
    assert lines[2:] == sorted(set(lines[2:])), 'Unsorted/duplicate aggregate'
    print(f'{len(old)} old theory modules conserved; nine additive Reader/Writer modules.')


def compiled_check():
    data = json.loads((ROOT/'docs/READER_WRITER_FOLD_CONTRACTS.json').read_text())
    assert data['baseline'] == BASELINE
    actual = query([e['name'] for e in data['endpoints']])
    compare(data['endpoints'], actual)
    for item in actual:
        assert not logical_axioms(item['assumptions']), item['name']
        assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal|SemanticMeasure', item['type']), item['name']
        if item['name'].endswith(('readerT_iteration_uniform', 'writerT_iteration_uniform')):
            assert 'iteration_uniform' in item['type'], item['name']
        if item['name'].endswith(('writerT_monad_laws', 'itree_fold_run_writer', 'itree_writer_fold_bind')):
            assert 'MonoidLaws' in item['type'], item['name']
        if item['name'].endswith(('itree_fold_run_reader', 'itree_fold_run_writer')):
            assert 'itree F' in item['type'], item['name']
    print(f'{len(actual)} axiom-free compiled contracts; generic laws, explicit ITree squares.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
