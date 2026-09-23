#!/usr/bin/env python3
"""End-to-end client: probability rewrite, State preservation, extracted runner."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = '60e1e77'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
NEW = 'theories/Examples/StateRewrite.v'
IMPORT = 'Require PTree.Examples.StateRewrite.'
ENDPOINTS = ['PTree.Examples.StateRewrite.' + n for n in [
    'preparation_sampling_fusion', 'source_program_rewrite', 'rewrite_then_handle',
    'original_counter', 'rewritten_counter', 'original_preparation_trace',
    'rewritten_preparation_trace', 'original_needs_an_extra_transition',
    'fused_missing_mass_is_not_normalized', 'preparation_success_probability',
    'preparation_other_probability', 'preparation_lost_probability',
    'rewritten_trace_has_operational_path']]


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def previous_sources(sources):
    if NEW not in sources:
        return sources
    code = without_comments(sources[NEW])
    assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code)
    for required in ['peutt_prob_flatten', 'run_state_peutt_eq', 'rational_attempts',
                     'original_needs_an_extra_transition', 'fused_missing_mass_is_not_normalized']:
        assert required in code, required
    result = {p: s for p, s in sources.items() if p != NEW}
    assert result[ALL].splitlines().count(IMPORT) == 1
    result[ALL] = result[ALL].replace(IMPORT + '\n', '')
    return result


def previous_extraction(text):
    if 'From PTree.Examples Require Import StateRewrite.' not in text:
        return text
    expected = frozen('extraction/rational-state/Extract.v.in')
    new = expected.replace('From PTree.Examples Require Import RationalState.\n',
        'From PTree.Examples Require Import RationalState.\nFrom PTree.Examples Require Import StateRewrite.\n')
    new = new.replace('rational_counter ticket_replay_source.',
                      'rational_counter ticket_replay_source original_counter rewritten_counter.')
    assert text == new, 'Only add two extracted proof-linked program roots'
    return expected


def check_source(sources):
    old = {p for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
           cwd=ROOT, text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | {NEW}
    prior = previous_sources(sources)
    for p in old:
        assert prior[p] == frozen(p), 'Frozen theory changed: ' + p
    lines = sources[ALL].splitlines()
    assert lines[2:] == sorted(set(lines[2:]))
    for p in ['docs/CONTRACTS.json', 'docs/MATHCOMP_DIRECT_CONTRACTS.json',
              'docs/EFFECT_EXECUTION_CONTRACTS.json', 'docs/HANDLER_MACHINE_CONTRACTS.json',
              'docs/STATE_PRESERVATION_CONTRACTS.json', 'docs/STANDARD_EFFECTS_CONTRACTS.json',
              'docs/STATE_FOLD_CONTRACTS.json', 'docs/RATIONAL_TICKETS_CONTRACTS.json']:
        assert (ROOT/p).read_text() == frozen(p), 'Frozen snapshot changed: ' + p
    previous_extraction((ROOT/'extraction/rational-state/Extract.v.in').read_text())
    driver = (ROOT/'extraction/rational-state/main.ml').read_text()
    for name in ['Rational.original_counter', 'Rational.rewritten_counter', 'Rational.rational_counter']:
        assert name in driver
    print(f'{len(old)} prior theory modules unchanged; one end-to-end example.')


def compiled_check():
    data = json.loads((ROOT/'docs/STATE_REWRITE_CONTRACTS.json').read_text())
    assert data['baseline'] == BASELINE
    actual = query(ENDPOINTS)
    compare(data['endpoints'], actual)
    # A PTree client may inherit the exact assumptions of its frozen generic
    # fusion theorem. Do not expand the independent Domain/sampler whitelist.
    contracts = json.loads(frozen('docs/CONTRACTS.json'))['endpoints']
    fusion = next(e for e in contracts if e['name'] == 'PTree.Eq.PEutt.peutt_prob_flatten')
    inherited_fusion = logical_axioms(fusion['assumptions'])
    for item in actual:
        allowed = SOUNDNESS_AXIOMS | (inherited_fusion if item['name'] in ENDPOINTS[:3] else set())
        assert logical_axioms(item['assumptions']) <= allowed, item['name']
    assert 'canonical_peutt' in actual[2]['type'], 'Must use the selected public behavior'
    print(f'{len(actual)} compiled contracts; only the three proof clients inherit frozen fusion choice axioms.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
