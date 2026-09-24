#!/usr/bin/env python3
"""ExceptT laws and fold square; preserve existing interpreters and semantics."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, without_comments

BASELINE = '9431e4b'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
MODULES = ['Core/ExceptT', 'Interp/ExceptionFold', 'Interp/ExceptionFoldFacts',
           'Regression/Semantics/ExceptionFold']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def check_new(sources):
    assert NEW <= set(sources), 'Incomplete exception transformer increment'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
        assert not re.search(r'#\[global\]|Global (?:Instance|Existing)', code), p
        if '/Regression/' not in p:
            assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal|SemanticMeasure|Prob\.', code), p
    core = without_comments(sources['theories/Core/ExceptT.v'])
    for token in ['eitherT Err T', 'exceptT_monad_laws', 'exceptT_iteration_uniform',
                  '(Hunif : @iteration_uniform T MT IT QT)', '@MonadIter_eitherT']:
        assert token in core, token
    assert not re.search(r'\b(?:Inductive|CoInductive|Fixpoint|CoFixpoint)\b', core)
    square = without_comments(sources['theories/Interp/ExceptionFoldFacts.v'])
    for token in ['exception_fold_square', 'fold_run_exception', 'observe_run_exception',
                  '(Hunif : @iteration_uniform T MT IT QT)', 'apply (Hunif']:
        assert token in square, token
    reg = sources['theories/Regression/Semantics/ExceptionFold.v']
    for token in ['exception_target_monad', 'exception_target_uniform', 'itree_iteration_uniform',
                  'CoFixpoint retry_or_throw', 'sample_then_exception', 'Constraint Set < high',
                  'Fail Check PTree.Eq.PEutt.peutt.']:
        assert token in reg, token


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
    print(f'{len(old)} old theory modules conserved; four additive exception-transformer modules.')


def compiled_check():
    data = json.loads((ROOT/'docs/EXCEPTION_FOLD_CONTRACTS.json').read_text())
    assert data['baseline'] == BASELINE
    actual = query([e['name'] for e in data['endpoints']])
    compare(data['endpoints'], actual)
    for item in actual:
        # These algebraic proofs require no classical or extensional axioms.
        assert not logical_axioms(item['assumptions']), item['name']
        assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal|SemanticMeasure', item['type']), item['name']
        if item['name'].endswith(('fold_run_exception', 'exceptT_iteration_uniform')):
            assert 'iteration_uniform' in item['type'], item['name']
    print(f'{len(actual)} compiled contracts; no logical axioms or probability capabilities.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
