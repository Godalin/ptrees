#!/usr/bin/env python3
"""Additive relational-limit mathematics; existing interfaces and theory frozen."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = '6f79c1974cc3f82066cbb3326fcfff90c4ebb21f'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
NEW = {'theories/' + p + '.v' for p in [
    'Prob/Interface/RelationalLimit', 'Prob/Domain/RelationalLimit',
    'Prob/Backend/Common/CountableRelationalLimit', 'Regression/Probability/RelationalLimit']}
IMPORTS = {'Require PTree.' + p.removeprefix('theories/').removesuffix('.v').replace('/', '.') + '.'
           for p in NEW}
ENDPOINTS = ['PTree.' + module + '.' + name for module, names in {
    'Prob.Interface.RelationalLimit': ['sem_lift_lub_of_joint_chain'],
    'Prob.Domain.RelationalLimit': ['oval_dual_lub', 'oval_bidual_lub', 'oval_ae_lub',
                                    'oval_countably_supported_lub'],
    'Prob.Backend.Common.CountableRelationalLimit': ['oval_coupled_lub_of_countable_limits',
                                                    'oval_coupled_lub', 'oval_coupled_lub_witnesses'],
    'Regression.Probability.RelationalLimit': ['arbitrary_nat_relational_limit', 'successor_limit',
        'equality_limit', 'empty_relation_zero_limit', 'half_le_fair', 'initial_joint',
        'final_joint', 'final_joint_no_diagonal', 'initial_joint_has_no_increasing_extension',
        'growing_marginals_increasing', 'growing_marginals_coupled',
        'no_increasing_joint_selection', 'noncoherent_chain_has_limit_joint',
        'mathcomp_coherent_joint_limit'],
}.items() for name in names]


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def previous_sources(sources):
    """Exact additive projection for the frozen, earlier migration gate.

    Only this increment's four files and four aggregate lines are removed.
    Unknown modules, changes to old proofs, and duplicate imports remain visible.
    This increment has its own source/compiled audit; the old gate is not relaxed.
    """
    from audit_relational_consumers import previous_sources as consumer_sources
    sources = consumer_sources(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    for line in IMPORTS:
        assert result[ALL].splitlines().count(line) == 1, 'Missing/duplicate new import: ' + line
        result[ALL] = result[ALL].replace(line + '\n', '')
    return result


def check_source(sources):
    from audit_relational_consumers import previous_sources as consumer_sources
    sources = consumer_sources(sources)
    old = {p for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
           cwd=ROOT, text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW, 'Unexpected module addition/deletion'
    previous = previous_sources(sources)
    for p in old:
        assert previous[p] == frozen(p), 'Frozen source changed: ' + p
    lines = sources[ALL].splitlines()
    assert lines[2:] == sorted(set(lines[2:])), 'Unsorted/duplicate aggregate'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|Class|Instance|Hint)\b|Unset .*Checking', code), p
        if '/Regression/' not in p:
            assert not re.search(r'FreeOmega|MathCompKernel|ptree|FOQL', code), p
    generic = without_comments(sources['theories/Prob/Interface/RelationalLimit.v'])
    assert 'sem_increasing joints' in generic
    for ingredient in ['sem_lub_exists', 'sem_lub_proper', 'sem_bind_lub', 'sem_ae_lub', 'sem_lift_bind']:
        assert ingredient in generic, 'Missing joint-chain proof ingredient: ' + ingredient
    countable = without_comments(sources['theories/Prob/Backend/Common/CountableRelationalLimit.v'])
    for ingredient in ['oval_bidual_coupled', 'oval_bidual_lub', 'oval_countably_supported_lub']:
        assert ingredient in countable, 'Missing countable limit ingredient: ' + ingredient
    for premise in ['(forall n, oval_countably_supported (c n))',
                    '(forall n, oval_countably_supported (d n))',
                    '(Hc : oval_increasing c)', '(Hd : oval_increasing d)']:
        assert premise in countable, 'Missing support/order condition: ' + premise
    assert not re.search(r'\b(?:Hypothesis|Variable)\s+(?:joint|transport|realization)', countable)
    for p in ['docs/CONTRACTS.json', 'docs/MATHCOMP_DIRECT_CONTRACTS.json']:
        assert (ROOT / p).read_text() == frozen(p), 'Frozen compiled snapshot changed: ' + p
    print(f'{len(old)} prior theory modules unchanged except four exact aggregate additions.')


def compiled_check():
    results = query(ENDPOINTS, sorted({e.rsplit('.', 1)[0] for e in ENDPOINTS}))
    snapshot = json.loads((ROOT / 'docs/RELATIONAL_LIMIT_CONTRACTS.json').read_text())
    assert snapshot['baseline'] == BASELINE
    compare(snapshot['endpoints'], results)
    for result in results:
        assert logical_axioms(result['assumptions']) <= SOUNDNESS_AXIOMS, result['name']
        if result['name'].startswith('PTree.Prob.'):
            assert not re.search(r'FreeOmega|MathCompKernel|ptree', result['type']), result['name']
        if result['name'].startswith('PTree.Prob.Interface.'):
            assert result['assumptions'].strip() == 'Closed under the global context'
    print(f'{len(results)} relational-limit endpoints checked; existing logical-axiom whitelist unchanged.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text()
                  for p in (ROOT / 'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
