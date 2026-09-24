"""Finite probability bridge: preserve implementations, check laws and assumptions."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = '892a6d3'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
MODULES = ['Execution/Backend/FiniteDistribution', 'Execution/Backend/UniformReplay',
           'Execution/Validation/SubEnumQ', 'Regression/Execution/FiniteDistribution']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}
ENDPOINTS = ['PTree.' + m + '.' + n for m, names in {
    'Execution.Backend.FiniteDistribution': ['outcome_distribution_nonnegative',
        'outcome_expectation_prob', 'outcome_distribution_mass', 'outcome_distribution_no_entropy_failure'],
    'Execution.Backend.UniformReplay': ['fresh_uniform_entropy', 'replay_prob_cons',
        'finite_runner_distribution', 'trace_distribution_mass', 'replay_no_entropy_failure',
        'trace_distribution_nonnegative'],
    'Execution.Validation.SubEnumQ': ['finite_runner_hitting', 'replay_hitting',
        'replay_hitting_limit', 'return_head_test_bounded', 'runner_stable_hitting_adequacy'],
    'Regression.Execution.FiniteDistribution': ['first_attempt_outcomes', 'two_attempt_outcomes',
        'actual_runner_two_attempts', 'eliminated_state_distribution',
        'divergence_is_timeout_not_loss', 'missing_mass_is_not_timeout',
        'ret_requires_no_fuel', 'zero_fuel_draw_requests_no_entropy', 'biased_entropy_rejected',
        'correlated_history_rejected', 'higher_universe_execution', 'arbitrary_fuel_hitting', 'unbounded_retry_limit'],
}.items() for n in names]


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def check_new(sources):
    assert NEW <= set(sources), 'Incomplete finite probability bridge'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
    for name in ['FiniteDistribution', 'UniformReplay']:
        code = without_comments(sources[f'theories/Execution/Backend/{name}.v'])
        assert not re.search(r'FreeOmega|OmegaVal|SemanticMeasure|Classical|PTree\.Eq|Validation', code), name
    code = without_comments(sources['theories/Execution/Backend/UniformReplay.v'])
    for required in ['uniform_entropy', 'source history (ticket_count mu)', 'i :: history',
                     'run (@ticket_replay)', 'uniform_ticket_expectation', 'Hsource']:
        assert required in code, required
    code = without_comments(sources['theories/Execution/Validation/SubEnumQ.v'])
    for required in ['ptree_domain_approx', 'finite_runner_distribution',
                     'stable_hitting_denotational_adequacy', 'return_head_test_bounded']:
        assert required in code, required


def previous_sources(sources):
    from audit_handler_calculus import previous_sources as before_handlers
    sources = before_handlers(sources)
    if not (NEW & set(sources)):
        return sources
    check_new(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    for line in IMPORTS:
        assert result[ALL].splitlines().count(line) == 1, 'Missing/duplicate import: ' + line
        result[ALL] = result[ALL].replace(line + '\n', '')
    return result


def check_source(sources):
    from audit_handler_calculus import previous_sources as before_handlers
    sources = before_handlers(sources)
    old = {p for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
           cwd=ROOT, text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW
    prior = previous_sources(sources)
    for p in old:
        assert prior[p] == frozen(p), 'Frozen theory changed: ' + p
    lines = sources[ALL].splitlines()
    assert lines[2:] == sorted(set(lines[2:])), 'Unsorted/duplicate aggregate'
    tracked = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
                                     cwd=ROOT, text=True).splitlines()
    for p in tracked:
        if p.startswith('docs/') and (p.endswith('_CONTRACTS.json') or p == 'docs/CONTRACTS.json'):
            assert (ROOT/p).read_text() == frozen(p), 'Frozen snapshot changed: ' + p
        if p.startswith('extraction/'):
            assert (ROOT/p).read_text() == frozen(p), 'Runtime changed: ' + p
    print(f'{len(old)} prior theory modules and extraction unchanged; four additive bridge modules.')


def compiled_check():
    data = json.loads((ROOT/'docs/RUNNER_DISTRIBUTION_CONTRACTS.json').read_text())
    assert data['baseline'] == BASELINE
    actual = query(ENDPOINTS)
    compare(data['endpoints'], actual)
    for item in actual:
        axioms = logical_axioms(item['assumptions'])
        assert axioms <= SOUNDNESS_AXIOMS, item['name']
        if '.Execution.Backend.' in item['name']:
            assert not axioms, item['name']
    print(f'{len(actual)} compiled contracts; finite operational proofs axiom-free; external bridge uses existing whitelist.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
