#!/usr/bin/env python3
"""Handler calculus: preserve old semantics, expose one generic proof owner."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = 'a8275df'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
MODULES = [
    'Core/Handler', 'Interp/RelationalPreservation', 'Interp/HandlerRelation',
    'Interp/HandlerFacts', 'Interp/FreeOmega/HandlerCompletion',
    'Regression/Infrastructure/PublicHandlers', 'Regression/Semantics/HandlerCalculus',
]
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}
CHANGED = {
    'theories/Interp/Preservation.v', 'theories/Interp/Unrestricted.v',
    'theories/PTree.v', 'theories/PTreeFacts.v',
    'theories/Regression/Infrastructure/ArchitectureBoundaries.v',
}
ENDPOINTS = ['PTree.' + m + '.' + n for m, names in {
    'Core.Handler': ['Handler', 'id_', 'cat', 'case_', 'inl_', 'inr_', 'bimap', 'empty'],
    'Interp.RelationalPreservation': ['interp_rel_vis_fusion', 'peutt_interp_rel_of_vis_fusion'],
    'Interp.HandlerRelation': ['peutt_handler', 'peutt_handler_equivalence', 'handler_pair_kernel',
        'handler_pair_complete', 'handler_pair_vis_fusion', 'peutt_interp_handler_rel',
        'peutt_interp_handler_Proper', 'peutt_interp_handler_polymorphic_Proper'],
    'Interp.HandlerFacts': ['handler_finite_front_ret', 'handler_complete_front_ret',
        'peutt_interp_identity', 'peutt_interp_trigger_event', 'handler_cat_congr',
        'handler_cat_id_l', 'handler_cat_id_r', 'handler_cat_assoc',
        'handler_case_congr', 'handler_case_inl', 'handler_case_inr', 'handler_case_eta',
        'handler_case_eta_cat', 'handler_case_cat', 'handler_empty_unique',
        'handler_bimap_congr', 'handler_cat_Proper'],
    'Interp.FreeOmega.HandlerCompletion': ['free_omega_peutt_interp_handler_rel',
        'free_omega_peutt_interp_handler_Proper', 'free_omega_peutt_interp_handler_polymorphic_Proper',
        'free_omega_handler_cat_congr', 'free_omega_handler_cat_id_l',
        'free_omega_handler_cat_id_r', 'free_omega_handler_cat_assoc',
        'free_omega_handler_case_inl', 'free_omega_handler_case_inr', 'free_omega_handler_bimap_congr'],
    'Regression.Infrastructure.PublicHandlers': ['replacement_not_structural',
        'public_handler_replacement', 'returning_handlers_on_infinite_source',
        'different_return_carriers', 'rewriting_handler', 'public_left_unit',
        'public_right_unit', 'public_associativity', 'public_case_beta',
        'public_bimap_replacement', 'high_handler'],
    'Regression.Semantics.HandlerCalculus': ['real_sampling_handler_rel',
        'real_infinite_sampling', 'real_handler_bind_client', 'real_right_identity'],
}.items() for n in names]


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def replace_proof(text, theorem, proof):
    start = re.search(r'\bTheorem ' + re.escape(theorem) + r'\s', text).start()
    a = text.index('Proof.', start)
    b = text.index('Qed.', a) + len('Qed.')
    return text[:a] + proof + text[b:]


def expected(path):
    text = frozen(path)
    if path.endswith('/Preservation.v'):
        text = text.replace('Require Import Kernel Scheduling.',
                            'Require Import Kernel Scheduling RelationalPreservation.')
        return replace_proof(text, 'peutt_interp_of_vis_fusion', '''Proof.
  apply (peutt_interp_rel_of_vis_fusion (handler1 := handler) (handler2 := handler)).
  exact Hvis.
Qed.''')
    if path.endswith('/Unrestricted.v'):
        text = text.replace('Import Kernel Preservation HandlerMachine HandlerMachineAcceleration.',
                            'Import Kernel Preservation HandlerMachine HandlerMachineAcceleration\n  HandlerRelation.')
        return replace_proof(text, 'peutt_interp', '''Proof.
  apply (peutt_interp_handler_rel Hzero Hlimit).
  intros X e. apply peutt_refl.
Qed.''')
    if path == 'theories/PTree.v':
        return text.replace('From PTree.Core Require Export PTreeDefinition.',
                            'From PTree.Core Require Export PTreeDefinition Handler.')
    if path == 'theories/PTreeFacts.v':
        return text.replace('From PTree.Interp Require Export Guarded.\n'
                            'From PTree.Interp.FreeOmega Require Export Atomic MDP.',
                            'From PTree.Interp Require Export Guarded Unrestricted HandlerRelation HandlerFacts\n'
                            '  State Reader Writer Exception StateFacts StatePreservation StandardFacts ExceptionFacts.\n'
                            'From PTree.Interp.FreeOmega Require Export Atomic MDP HandlerCompletion.')
    if path.endswith('/ArchitectureBoundaries.v'):
        text = text.replace('Check @bind.\n', 'Check @bind.\nCheck @Handler.cat.\n')
        return text.replace('Check @ptree_bind_cofinal_all.\n',
            'Check @ptree_bind_cofinal_all.\n' +
            ''.join('Check @' + n + '.\n' for n in ['peutt_interp_handler_rel',
                'free_omega_peutt_interp_handler_rel', 'handler_cat_assoc', 'run_state_peutt',
                'run_reader_peutt', 'run_writer_peutt', 'run_exception_peutt']))
    raise AssertionError(path)


def check_new(sources):
    assert NEW <= set(sources), 'Incomplete handler calculus'
    assert CHANGED <= set(sources), 'Missing retained theorem owner or public entry point'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
        assert not re.search(r'#\[global\]|Global (?:Instance|Existing)', code), p
        if p.startswith('theories/Interp/') and '/FreeOmega/' not in p:
            assert not re.search(r'FreeOmega|MathComp|OmegaVal|Eq\.Internal|Prob\.Domain', code), p
    core = without_comments(sources['theories/Core/Handler.v'])
    assert not re.search(r'Semantic|peutt|Prob\.|Interp\.|Eq\.', core)
    rel = without_comments(sources['theories/Interp/HandlerRelation.v'])
    for token in ['active1 active2', 'peutt_state_hitting_lift', 'stable_hitting_rel',
                  'handler_machine_hitting_sound', 'handler_pair_vis_fusion',
                  'peutt_interp_rel_of_vis_fusion', 'relational_lub FO']:
        assert token in rel, 'Missing two-handler proof stage: ' + token
    specialization = without_comments(sources['theories/Interp/FreeOmega/HandlerCompletion.v'])
    assert not re.search(r'\b(?:induction|cofix|coinduction)\b', specialization)
    public = sources['theories/Regression/Infrastructure/PublicHandlers.v']
    for token in ['setoid_rewrite H', 'replacement_not_structural', 'Constraint Set < hi',
                  'different_return_carriers', 'returning_handlers_on_infinite_source']:
        assert token in public, 'Missing client contract: ' + token
    for p in CHANGED:
        assert sources[p] == expected(p), 'Unauthorized old-source edit: ' + p


def previous_sources(sources):
    """Validate this increment, then reconstruct the exact previous snapshot."""
    from audit_itree_bridge import previous_sources as previous_bridge
    sources = previous_bridge(sources)
    if not (NEW & set(sources)):
        return sources
    check_new(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    for p in CHANGED:
        result[p] = frozen(p)
    for line in IMPORTS:
        assert result[ALL].splitlines().count(line) == 1, 'Missing/duplicate import: ' + line
        result[ALL] = result[ALL].replace(line + '\n', '')
    return result


def check_source(sources):
    from audit_itree_bridge import previous_sources as previous_bridge
    sources = previous_bridge(sources)
    old = {p for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
               cwd=ROOT, text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW, 'Unapproved theory addition/deletion'
    prior = previous_sources(sources)
    for p in old:
        assert prior[p] == frozen(p), 'Frozen theory changed: ' + p
    lines = sources[ALL].splitlines()
    assert lines[2:] == sorted(set(lines[2:])), 'Unsorted/duplicate aggregate'
    tracked = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
                                     cwd=ROOT, text=True).splitlines()
    for p in tracked:
        if p.startswith('docs/') and (p.endswith('_CONTRACTS.json') or p == 'docs/CONTRACTS.json'):
            assert (ROOT/p).read_text() == frozen(p), 'Existing snapshot changed: ' + p
    print(f'{len(old)} old modules conserved except exact proof delegation/public exports; seven new modules.')


def compiled_check():
    data = json.loads((ROOT/'docs/HANDLER_CALCULUS_CONTRACTS.json').read_text())
    assert data['baseline'] == BASELINE
    actual = query(ENDPOINTS)
    compare(data['endpoints'], actual)
    for item in actual:
        assert logical_axioms(item['assumptions']) <= SOUNDNESS_AXIOMS, item['name']
        if item['name'] == 'PTree.Interp.HandlerRelation.peutt_handler_equivalence':
            assert logical_axioms(item['assumptions']) <= {'Eqdep.Eq_rect_eq.eq_rect_eq'}
        elif item['name'].startswith(('PTree.Interp.HandlerRelation.', 'PTree.Interp.RelationalPreservation.')):
            assert not logical_axioms(item['assumptions']), item['name']
    from audit_handler_machine import compiled_check as original
    original()
    old = json.loads((ROOT/'docs/GENERIC_CONSUMER_CONTRACTS.json').read_text())
    retained = [e for e in old['endpoints'] if e['name'].startswith(
        ('PTree.Interp.Preservation.', 'PTree.Interp.Guarded.'))]
    assert retained, 'Missing original fusion/guarded contracts'
    compare(retained, query([e['name'] for e in retained]))
    print(f'{len(actual)} new compiled handler contracts; original handler and '
          f'{len(retained)} fusion/guarded signatures/assumptions unchanged.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
