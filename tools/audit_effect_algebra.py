#!/usr/bin/env python3
"""Finite interpreted-effect algebra; no source equivalence or new capability."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = '6debbab'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
MODULES = ['Interp/Algebra/Computation', 'Interp/Algebra/Reader', 'Interp/Algebra/State',
           'Interp/Algebra/Writer', 'Interp/Algebra/Exception',
           'Examples/EffectInteractions', 'Regression/Semantics/EffectAlgebra']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def check_new(sources):
    assert NEW <= set(sources), 'Incomplete interpreted effect algebra'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
        assert not re.search(r'#\[global\]|Global (?:Instance|Existing)', code), p
        if p.startswith('theories/Interp/'):
            assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal|Prob\.Domain', code), p
    for owner, names in {
        'Reader': ['run_reader_ask_ask', 'run_reader_prob', 'run_reader_ask_prob'],
        'State': ['run_state_get_get', 'run_state_get_put', 'run_state_put_get',
                  'run_state_put_put', 'run_state_prob', 'run_state_get_prob', 'run_state_put_prob'],
        'Writer': ['run_writer_bind', 'run_writer_tell_unit', 'run_writer_tell_append',
                   'run_writer_prob', 'run_writer_tell_prob'],
        'Exception': ['run_exception_bind', 'run_exception_throw_bind', 'run_exception_prob'],
    }.items():
        code = without_comments(sources['theories/Interp/Algebra/' + owner + '.v'])
        for n in names:
            assert re.search(r'\bTheorem\s+' + n + r'\b', code), n
    writer = without_comments(sources['theories/Interp/Algebra/Writer.v'])
    assert 'MonoidLaws W op' in writer and 'monoid_plus op log w' in writer
    assert 'Commutative' not in writer
    reg = sources['theories/Regression/Semantics/EffectAlgebra.v']
    for token in ['sampling_before_throw_not_erasable', 'free_omega_qlift_upper_mass',
                  'partial_error_hitting', 'log_monoid_not_commutative', 'half_entries']:
        assert token in reg, 'Missing boundary: ' + token
    example = sources['theories/Examples/EffectInteractions.v']
    for token in ['itree (probE SubEnumQ', 'lower_then_count',
                  'count_sample_transformer_agreement', 'iteration_uniform']:
        assert token in example


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
    print(f'{len(old)} old theory modules conserved; seven additive interpreted-algebra modules.')


def compiled_check():
    data = json.loads((ROOT/'docs/EFFECT_ALGEBRA_CONTRACTS.json').read_text())
    assert data['baseline'] == BASELINE
    actual = query([e['name'] for e in data['endpoints']])
    compare(data['endpoints'], actual)
    # The generic Prob congruence already uses Coq's relational/unique
    # choice. Bound these consumers by its FROZEN contract, rather than
    # silently broadening the external-model SOUNDNESS_AXIOMS whitelist.
    baseline = json.loads(frozen('docs/CONTRACTS.json'))
    prob = next(e for e in baseline['endpoints'] if e['name'] == 'PTree.Eq.PEutt.peutt_prob')
    prob_axioms = logical_axioms(prob['assumptions'])
    prob_consumers = {
        'PTree.Interp.Algebra.Reader.run_reader_ask_prob',
        'PTree.Interp.Algebra.State.run_state_get_prob',
        'PTree.Interp.Algebra.State.run_state_put_prob',
        'PTree.Interp.Algebra.Writer.run_writer_tell_prob',
        'PTree.Examples.EffectInteractions.lower_then_count',
        'PTree.Regression.Semantics.EffectAlgebra.state_draw_swap',
        'PTree.Regression.Semantics.EffectAlgebra.writer_draw_swap',
        'PTree.Regression.Semantics.EffectAlgebra.real_state_draw_swap',
    }
    for item in actual:
        allowed = SOUNDNESS_AXIOMS | (prob_axioms if item['name'] in prob_consumers else set())
        assert logical_axioms(item['assumptions']) <= allowed, item['name']
        if item['name'].startswith('PTree.Interp.Algebra.'):
            assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal', item['type']), item['name']
        if item['name'].endswith(('run_writer_tell_unit', 'run_writer_tell_append')):
            assert 'MonoidLaws' in item['type'], item['name']
        if item['name'].endswith(('run_state_get_get', 'run_state_put_put', 'run_reader_ask_ask')):
            assert 'relational_lub' not in item['type'], item['name']
    print(f'{len(actual)} compiled effect contracts; Prob consumers bounded by the frozen '
          'peutt_prob choice assumptions, other endpoints by the unchanged soundness whitelist.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
