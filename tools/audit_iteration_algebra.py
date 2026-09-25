#!/usr/bin/env python3
"""Behavioral monad laws, pure-map uniformity, and the full-interface boundary."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments
from audit_mathcomp_direct import parse_direct

BASELINE = 'd864423b'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
DIRECT = 'theories/Regression/Backend/MathCompDirect.v'
MODULES = ['Interp/IterationAlgebra', 'Interp/FreeOmega/IterationAlgebra',
           'Regression/Semantics/PTreeIterationAlgebra']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}
DIRECT_APPEND = """
(** Explicit monad laws and pure-map uniformity, still conditional on native
    relational-lub closure and confined to this existing direct client. *)
From ITree.Basics Require Import Basics Monad.
From PTree.Core Require Import IterationLaws.
From PTree.Interp Require Import IterationAlgebra.
Section BehavioralIterationAlgebra.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E : Type -> Type}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation Q := (ptree_peutt_eq1 (E := E) (FI := NI)).
Variable Hlimit : relational_lub NO.

Example direct_monad_laws_of_relational_lub :
  @MonadLawsE (ptree E M) Q Monad_ptree.
Proof.
  exact (ptree_peutt_monad_laws (@mathcomp_relational_mixed_bind R)
    (@mathcomp_relational_zero R) Hlimit).
Qed.

Example direct_uniformity_of_relational_lub {I J A}
    (f : I -> ptree E M (I+A)) (g : J -> ptree E M (J+A)) (h : I -> J) :
  (forall i, @eq1 _ Q _
    (PTree.bind (f i) (fun v => Ret (iteration_map h v))) (g (h i))) ->
  forall i, @eq1 _ Q _ (PTree.iter f i) (PTree.iter g (h i)).
Proof.
  apply (peutt_iter_uniform (@mathcomp_relational_mixed_bind R)
    (@mathcomp_relational_zero R) Hlimit).
Qed.
End BehavioralIterationAlgebra.
"""

@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)

def check_new(sources):
    assert NEW <= set(sources), 'Incomplete iteration algebra increment'
    assert sources[DIRECT] == frozen(DIRECT) + DIRECT_APPEND, 'Unapproved Gate M edit'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
        assert not re.search(r'#\[global\]|Global (?:Instance|Existing)', code), p
    core = without_comments(sources['theories/Interp/IterationAlgebra.v'])
    assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal|Backend|\bclassic\b|Classical', core)
    for token in ['ptree_peutt_eq1', 'ptree_peutt_equivalence', 'ptree_peutt_monad_laws',
                  'pstruct_return_map', 'peutt_iter_eventful_rel', 'peutt_iter_uniform',
                  'ptree_peutt_iter_unfold', 'ptree_peutt_iter_finite_stutter']:
        assert token in core, token
    assert not re.search(r'(?:Definition|Theorem)\s+ptree_peutt_iteration_uniform\b', core), \
        'Do not silently export the uninstantiable Eq1-wide package'
    thin = without_comments(sources['theories/Interp/FreeOmega/IterationAlgebra.v'])
    assert not re.search(r'\b(?:coinduction|induction|CoFixpoint|Inductive)\b', thin)
    reg = sources['theories/Regression/Semantics/PTreeIterationAlgebra.v']
    for token in ['actual_monad_rewriting', 'eq1_is_canonical', 'actual_uniformity',
                  'reader_inherits_monad', 'exception_inherits_monad', 'writer_inherits_monad',
                  'collapse_unbounded_counter', 'real_lawful_iteration', 'high_uniformity',
                  'Constraint Set < high', 'Fail Definition no_global_behavioral_eq1',
                  'Fail Definition protocol_uniformity_package', 'Fail Check PTree.Prob.Domain']:
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
    print(f'{len(old)} prior modules conserved, except exact aggregate and Gate M additions.')

def check_uniformity_boundary():
    """Check the failure reason, not merely that an arbitrary ill-typed probe fails."""
    script = '''
From PTree.Regression.Infrastructure Require Import AllImports.
From PTree.Core Require Import PTreeDefinition IterationLaws.
From ITree.Basics Require Import Basics Monad.
From PTree.Eq.Backend Require Import SubEnumQ.
From PTree.Interp.FreeOmega Require Import IterationAlgebra.
Set Universe Polymorphism.
Goal True. idtac "UNIFORM_BOUNDARY_START". Abort.
Definition unpackageable {F : Type -> Type} :
 @iteration_uniform (ptree F SubEnumQ) Monad_ptree MonadIter_ptree free_omega_ptree_eq1 :=
 fun I J A f g h => @free_omega_peutt_iter_uniform SubEnumQ _ _ _ _ _ _ F I J A f g h.
Goal True. idtac "UNIFORM_BOUNDARY_END". Abort.
'''
    result = subprocess.run(['opam', 'exec', '--', 'coqtop', '-quiet', '-R',
        '_build/default/theories', 'PTree'], cwd=ROOT, input=script,
        text=True, capture_output=True)
    assert result.returncode == 0, result.stderr
    assert result.stdout.count('UNIFORM_BOUNDARY_START') == 1
    assert result.stdout.count('UNIFORM_BOUNDARY_END') == 1
    errors = result.stdout + result.stderr
    assert errors.count('Error:') == 1 and 'universe inconsistency' in errors.lower(), errors
    print('Full-interface probe fails specifically by universe inconsistency; no stronger claim.')

def query_direct_algebra():
    names = ['PTree.Regression.Backend.MathCompDirect.' + n for n in
             ['direct_monad_laws_of_relational_lub', 'direct_uniformity_of_relational_lub']]
    names += ['PTree.Interp.IterationAlgebra.peutt_iter_uniform']
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
    data = json.loads((ROOT/'docs/ITERATION_ALGEBRA_CONTRACTS.json').read_text())
    assert data['baseline'] == BASELINE
    # Query after the entire safe aggregate, not only in a convenient standalone
    # import context: a polymorphic constant can typecheck alone yet be unusable.
    actual = query([e['name'] for e in data['endpoints']],
                   ['PTree.Regression.Infrastructure.AllImports'])
    compare(data['endpoints'], actual)
    for item in actual:
        assert logical_axioms(item['assumptions']) <= SOUNDNESS_AXIOMS, item['name']
        if item['name'].startswith('PTree.Interp.IterationAlgebra.'):
            assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal|Backend', item['type'])
            assert logical_axioms(item['assumptions']) <= {'Eqdep.Eq_rect_eq.eq_rect_eq'}
    direct = query_direct_algebra()
    assert direct == data['direct'], 'Gate M type/assumption/unsafe report drift'
    for item in direct[:2]:
        assert item['unsafe_hierarchy'] and item['session_collapsed_universes']
        assert 'MathCompCouplingGluing' in item['type'] and 'relational_lub' in item['type']
        assert logical_axioms(item['assumptions']) <= SOUNDNESS_AXIOMS
    assert not direct[2]['unsafe_hierarchy'], 'Safe generic theorem acquired an unsafe flag'
    check_uniformity_boundary()
    print(f'{len(actual)} safe contracts in the joint AllImports context; Gate M separately recorded.')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
