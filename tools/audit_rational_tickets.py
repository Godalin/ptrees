#!/usr/bin/env python3
"""Executable rational tickets: exact finite law, not a PRNG fairness claim."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = '09a1773'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
MODULES = ['Execution/Backend/RationalTickets', 'Examples/RationalState',
           'Regression/Execution/RationalTickets']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}
ENDPOINTS = ['PTree.' + module + '.' + name for module, names in {
    'Execution.Backend.RationalTickets': ['ticket_coefficient', 'compile_tickets_positive',
        'compile_tickets_expectation', 'compile_tickets_bound', 'ticket_outcomes_size',
        'ticket_outcomes_enumerated', 'uniform_ticket_expectation', 'uniform_ticket_returns',
        'uniform_ticket_loss', 'ticket_sample_valid', 'ticket_sample_invalid'],
    'Examples.RationalState': ['rational_counter', 'rational_ticket_layout', 'rational_two_attempts',
        'rational_missing_mass_stops', 'rational_timeout_no_redraw', 'rational_invalid_entropy_not_loss'],
    'Regression.Execution.RationalTickets': ['nonfair_success_mass', 'nonfair_retry_mass',
        'partial_loss_is_exact', 'arbitrary_signed_observable', 'zero_duplicates_keep_mass',
        'zero_mass_has_one_missing_ticket', 'no_entropy_is_not_loss',
        'last_valid_ticket_is_loss', 'bound_is_checked'],
}.items() for name in names]


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def check_new(sources):
    assert NEW <= set(sources), 'Incomplete rational ticket increment'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
    code = without_comments(sources['theories/Execution/Backend/RationalTickets.v'])
    assert not re.search(r'FreeOmega|MathComp|OmegaVal|SemanticMeasure|Classical|xchoose|epsilon', code)
    for text in ['numq p', 'denq p', 'List.repeat None', 'uniform_ticket_expectation',
                 '1 - enumQ_mass', 'else (NoEntropy, rest)']:
        assert text in code, text


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
              'docs/STATE_PRESERVATION_CONTRACTS.json', 'docs/STANDARD_EFFECTS_CONTRACTS.json',
              'docs/STATE_FOLD_CONTRACTS.json']:
        assert (ROOT/p).read_text() == frozen(p), 'Frozen snapshot changed: ' + p
    extract = (ROOT/'extraction/rational-state/Extract.v.in').read_text()
    assert 'Extraction "rational.ml" rational_counter ticket_replay_source.' in extract
    assert not re.search(r'Extract Constant|Extract Inductive|ExtrOcamlNatInt|ExtrOcamlZInt', extract)
    print(f'{len(old)} prior theory modules unchanged; verified tickets plus extracted State client.')


def compiled_check():
    snapshot = json.loads((ROOT/'docs/RATIONAL_TICKETS_CONTRACTS.json').read_text())
    assert snapshot['baseline'] == BASELINE
    actual = query(ENDPOINTS)
    compare(snapshot['endpoints'], actual)
    for item in actual:
        assert logical_axioms(item['assumptions']) <= SOUNDNESS_AXIOMS, item['name']
        if item['name'].startswith('PTree.Execution.'):
            assert not logical_axioms(item['assumptions']), item['name']
            assert not re.search(r'FreeOmega|OmegaVal|SemanticMeasure|realType', item['type'])
    print(f'{len(actual)} compiled contracts; rational sampler proofs have no logical axioms.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
