#!/usr/bin/env python3
"""Direct restart machine: full uniformity, real fold consumers, exact old-source conservation."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments
from audit_mathcomp_direct import parse_direct

BASELINE = '88e9cf2'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
DIRECT = 'theories/Regression/Backend/MathCompDirect.v'
MODULES = ['Interp/IterationMachine', 'Interp/IterationUniform',
           'Interp/FreeOmega/IterationUniform', 'Regression/Semantics/PTreeUniformity']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}
DIRECT_APPEND = """
(** Full Eq1-wide uniformity from the direct machine, not the protocol
    proof. Mathematical premises and the existing Gate M boundary remain. *)
From PTree.Interp Require Import IterationUniform.
Section FullIterationUniformity.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E : Type -> Type}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Variable Hlimit : relational_lub NO.

Example direct_full_uniformity_of_relational_lub :
  @iteration_uniform (ptree E M) Monad_ptree MonadIter_ptree
    (ptree_peutt_eq1 (FI := NI)).
Proof.
  exact (ptree_peutt_iteration_uniform (@mathcomp_relational_mixed_bind R)
    (@mathcomp_relational_zero R) Hlimit).
Qed.
End FullIterationUniformity.
"""

@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)

def check_new(sources):
    assert NEW <= set(sources), 'Incomplete direct iteration increment'
    assert sources[DIRECT] == frozen(DIRECT) + DIRECT_APPEND, 'Unapproved Gate M edit'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
        assert not re.search(r'#\[global\]|Global (?:Instance|Existing)', code), p
    for module in ['IterationMachine', 'IterationUniform']:
        code = without_comments(sources['theories/Interp/' + module + '.v'])
        assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal|Backend|\bclassic\b|Classical', code)
        assert not re.search(r'iteration_protocol|iteration_handler|peutt_iter_eventful|\biterationE\b', code)
        assert not re.search(r'\b(?:Variant|Inductive|CoInductive|CoFixpoint)\b', code), 'No auxiliary syntax'
    machine = without_comments(sources['theories/Interp/IterationMachine.v'])
    for token in ['iter_primitive_tree', 'iter_phase_grid_le_primitive',
                  'iter_primitive_le_phase_grid', 'iter_phase_diagonal_tree',
                  'sem_lub_double_diagonal', 'iter_machine_hitting_sound']:
        assert token in machine, token
    uniform = without_comments(sources['theories/Interp/IterationUniform.v'])
    for token in ['iter_direct_kernel_related', 'peutt_iter_active_rel',
                  'peutt_iter_direct_rel', 'stable_hitting_rel', 'iter_machine_hitting_sound',
                  'ptree_peutt_iteration_uniform', '@iteration_uniform']:
        assert token in uniform, token
    thin = without_comments(sources['theories/Interp/FreeOmega/IterationUniform.v'])
    assert not re.search(r'\b(?:coinduction|induction|Inductive|Fixpoint)\b', thin)
    reg = sources['theories/Regression/Semantics/PTreeUniformity.v']
    for token in ['full_uniformity', 'state_fold_into_ptree', 'exception_fold_into_ptree',
                  'fold_run_state', 'fold_run_exception', 'tree_state_uniformity',
                  'reader_inherits_full_uniformity', 'writer_inherits_full_uniformity',
                  'exception_inherits_full_uniformity', 'real_full_uniformity',
                  'high_full_uniformity', 'Constraint Set < high',
                  'Fail Check PTree.Prob.Domain', 'Fail Check PTree.Eq.Backend.MathComp']:
        assert token in reg, token

def previous_sources(sources):
    if not (NEW & set(sources)):
        return sources
    check_new(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    result[DIRECT] = frozen(DIRECT)
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
    print(f'{len(old)} prior modules conserved; direct iteration is additive, no universe/interface changes.')

def query_direct():
    names = ['PTree.Regression.Backend.MathCompDirect.direct_full_uniformity_of_relational_lub',
             'PTree.Interp.IterationUniform.ptree_peutt_iteration_uniform']
    commands = ['Local Unset Universe Checking.',
                'Require PTree.Regression.Backend.MathCompDirect.',
                'Set Printing Width 100.', 'Set Printing Depth 1000.', 'Set Printing Implicit.']
    for i, name in enumerate(names):
        for kind, command in [('TYPE', 'Check @' + name), ('AXIOMS', 'Print Assumptions ' + name), ('END', None)]:
            commands.append(f'Goal True. idtac "AUDIT_{kind}_{i}". Abort.')
            if command:
                commands.append(command + '.')
    result = subprocess.run(['opam', 'exec', '--', 'coqtop', '-quiet', '-R',
        '_build/default/theories', 'PTree'], cwd=ROOT, input='\n'.join(commands) + '\n',
        text=True, capture_output=True)
    return parse_direct(result, names)

def compiled_check():
    data = json.loads((ROOT/'docs/DIRECT_ITERATION_CONTRACTS.json').read_text())
    assert data['baseline'] == BASELINE
    actual = query([e['name'] for e in data['endpoints']],
                   ['PTree.Regression.Infrastructure.AllImports'])
    compare(data['endpoints'], actual)
    for item in actual:
        assert logical_axioms(item['assumptions']) <= SOUNDNESS_AXIOMS, item['name']
        if item['name'].startswith(('PTree.Interp.IterationMachine.', 'PTree.Interp.IterationUniform.')):
            assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal|Backend', item['type'])
            assert logical_axioms(item['assumptions']) <= {'Eqdep.Eq_rect_eq.eq_rect_eq'}
        if item['name'].endswith(('.ptree_peutt_iteration_uniform', '.full_uniformity',
                                  '.free_omega_ptree_iteration_uniform', '.real_full_uniformity')):
            assert 'iteration_uniform' in item['type'], 'Must be the full interface'
        if item['name'].endswith('.peutt_iter_direct_rel'):
            assert 'SemanticMeasure MN' not in item['type'], 'No native relational bridge needed'
            for token in ['relational_lub', 'relational_zero', 'pstruct_iter_sum_rel']:
                assert token in item['type'], token
    direct = query_direct()
    assert direct == data['direct'], 'Gate M type/assumption/unsafe flag drift'
    assert direct[0]['unsafe_hierarchy'] and direct[0]['session_collapsed_universes']
    assert not direct[1]['unsafe_hierarchy'], 'Safe generic proof acquired an unsafe flag'
    for token in ['MathCompCouplingGluing', 'relational_lub', 'iteration_uniform']:
        assert token in direct[0]['type'], token
    assert logical_axioms(direct[0]['assumptions']) <= SOUNDNESS_AXIOMS
    print(f'{len(actual)} safe contracts checked after AllImports, including full interface and fold clients.')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
