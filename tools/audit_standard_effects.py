#!/usr/bin/env python3
"""Thin standard effects over the frozen handler/State foundations."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = '081ee41'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
MODULES = ['Interp/Reader', 'Interp/Writer', 'Interp/Exception', 'Interp/StandardFacts',
           'Interp/ExceptionFacts', 'Regression/Semantics/StandardEffects']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}
ENDPOINTS = ['PTree.' + module + '.' + name for module, names in {
    'Interp.Reader': ['reader_handler', 'run_reader', 'reader_ask_returns', 'reader_residual_forwards'],
    'Interp.Writer': ['writer_handler', 'run_writer', 'writer_tell_appends'],
    'Interp.Exception': ['run_exception', 'exception_result_rel', 'observe_run_exception'],
    'Interp.StandardFacts': ['run_reader_bind', 'run_reader_peutt', 'run_writer_peutt'],
    'Interp.ExceptionFacts': ['run_exception_ret', 'run_exception_throw', 'run_exception_prob',
                             'exception_hitting_approx', 'exception_hitting', 'run_exception_peutt'],
    'Regression.Semantics.StandardEffects': ['reader_heterogeneous', 'writer_heterogeneous',
        'exception_heterogeneous', 'reader_native_probability', 'writer_chronological_order',
        'writer_probabilistic_other_branch', 'exception_is_a_returned_error', 'exception_success_branch',
        'missing_mass_is_not_an_exception', 'reader_forwards_event', 'writer_forwards_event',
        'infinite_exception_weak_rewrite'],
}.items() for name in names]


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def check_new(sources):
    assert NEW <= set(sources), 'Incomplete standard effects increment'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
        assert not re.search(r'#\[global\]|Global (?:Instance|Existing)', code), p
        assert not re.search(r'\b(?:Variant|Inductive)\s+(?:readerE|writerE|exceptE|stateE)', code), p
        if p.startswith('theories/Interp/'):
            assert not re.search(r'FreeOmega|MathComp|OmegaVal|Eq\.Internal|Prob\.Domain', code), p
    facts = without_comments(sources['theories/Interp/StandardFacts.v'])
    assert 'Unrestricted.peutt_interp' in facts and 'StatePreservation.run_state_peutt' in facts
    assert not re.search(r'\b(?:coinduction|cofix|induction)\b', facts)
    exc = without_comments(sources['theories/Interp/Exception.v'])
    assert 'inl1 ex => Ret (inl (exception_value ex))' in exc
    assert 'Prob mu (fun x => run_exception (k x))' in exc
    proof = without_comments(sources['theories/Interp/ExceptionFacts.v'])
    for name in ['exception_hitting_approx', 'sem_lub_cofinal', 'peutt_state_hitting_lift']:
        assert name in proof, name


def previous_sources(sources):
    from audit_state_fold import previous_sources as before_fold
    sources = before_fold(sources)
    if not (NEW & set(sources)):
        return sources
    check_new(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    for line in IMPORTS:
        assert result[ALL].splitlines().count(line) == 1, 'Missing/duplicate import: ' + line
        result[ALL] = result[ALL].replace(line + '\n', '')
    return result


def check_source(sources):
    from audit_state_fold import previous_sources as before_fold
    sources = before_fold(sources)
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
              'docs/STATE_PRESERVATION_CONTRACTS.json']:
        assert (ROOT/p).read_text() == frozen(p), 'Frozen snapshot changed: ' + p
    print(f'{len(old)} prior theory modules unchanged; six additive standard-effect modules.')


def compiled_check():
    snapshot = json.loads((ROOT/'docs/STANDARD_EFFECTS_CONTRACTS.json').read_text())
    assert snapshot['baseline'] == BASELINE
    actual = query(ENDPOINTS)
    compare(snapshot['endpoints'], actual)
    for item in actual:
        assert logical_axioms(item['assumptions']) <= SOUNDNESS_AXIOMS, item['name']
        if item['name'].startswith('PTree.Interp.'):
            assert not logical_axioms(item['assumptions']), item['name']
            assert not re.search(r'FreeOmega|OmegaVal|MathComp', item['type']), item['name']
        if item['name'] == 'PTree.Interp.ExceptionFacts.run_exception_peutt':
            assert not re.search(r'relational_lub|FubiniLaws|DiagonalLaws|OmegaSelection', item['type'])
    print(f'{len(actual)} compiled contracts; generic effect proofs are axiom-free.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
