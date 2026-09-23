#!/usr/bin/env python3
"""Stage 1 consumer extraction from ad8705f. No foundation redesign."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, without_comments, query, logical_axioms, SOUNDNESS_AXIOMS

BASELINE = 'ad8705f'
ALG = 'theories/Eq/Algebra.v'
FOALG = 'theories/Eq/FreeOmega/Algebra.v'
COUPLING = 'theories/Prob/Interface/Coupling.v'
MEASURE = 'theories/Prob/FreeOmega/Measure.v'
COINCIDENCE = 'theories/Semantics/FreeOmega/MDPCoincidenceFreeOmega.v'
PUBLIC = 'theories/Regression/Infrastructure/PublicBehavior.v'
DIRECT = 'theories/Regression/Backend/MathCompDirect.v'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
CLIENT = 'theories/Regression/Semantics/GenericAlgebra.v'
OLD_CLIENT = 'theories/Regression/Semantics/PEuttAlgebra.v'
NEW = {ALG, CLIENT}
CHANGED = {FOALG, COUPLING, MEASURE, COINCIDENCE, PUBLIC, DIRECT, ALL, OLD_CLIENT,
           'theories/PTreeFacts.v'}
RELOCATION = {'PTree.Eq.FreeOmega.Algebra.'+n: 'PTree.Eq.Algebra.'+n
              for n in ['peutt_bind_Proper', 'peutt_fmap_Proper']}
CORE = list(RELOCATION.values()) + [
    'PTree.Prob.Interface.Coupling.coupling_ae_implies_ae_lift',
    'PTree.Prob.FreeOmega.Measure.free_omega_observable_dirac_ae_laws']
CLIENT_NAMES = ['generic_bind_proper', 'generic_fmap_proper', 'derived_ae_lift',
    'free_omega_bind_Proper', 'free_omega_fmap_Proper',
    'free_omega_frontier_ae_lift', 'free_omega_frontier_dirac_ae',
    'real_bind_proper', 'real_fmap_proper']
PUBLIC_NAMES = ['public_bind_setoid', 'public_continuation_setoid', 'public_fmap_setoid']
DIRECT_NAMES = ['direct_bind_setoid', 'direct_continuation_setoid', 'direct_fmap_setoid']
ENDPOINTS = CORE + ['PTree.Regression.Semantics.GenericAlgebra.'+n for n in CLIENT_NAMES]
ENDPOINTS += ['PTree.Regression.Infrastructure.PublicBehavior.'+n for n in PUBLIC_NAMES]

@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE+':'+path], cwd=ROOT, text=True)

def code(s):
    return ' '.join(without_comments(s).split())

def check_source(sources):
    old = {p for p in subprocess.check_output(['git','ls-tree','-r','--name-only',BASELINE],
           cwd=ROOT,text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW, 'Unapproved module addition/deletion'
    for p in old - CHANGED:
        assert sources[p] == frozen(p), 'Unrelated source drift: '+p
    expected = frozen(FOALG).split('#[global] Instance peutt_bind_Proper')[0] + 'End FreeOmegaAlgebra.\n'
    expected = expected.replace('From PTree.Eq Require Import Shallow PEutt PStruct.',
        'From PTree.Eq Require Import Shallow PEutt PStruct.\nFrom PTree.Eq Require Export Algebra.')
    assert sources[FOALG] == expected, 'Non-Proper FreeOmega algebra changed'
    before = frozen(COINCIDENCE)
    a = before.index('(** A proof of an existing capability')
    b = before.index('Section FreeOmegaCoincidence.')
    lemma = before[a:b]
    assert sources[COINCIDENCE] == before[:a]+before[b:], 'Coincidence changed beyond relocation'
    assert sources[MEASURE] == frozen(MEASURE).replace('Section FreeOmegaObservableLaws.',
        lemma+'Section FreeOmegaObservableLaws.',1), 'DiracAE must move byte-for-byte'
    prefix = frozen(COUPLING).replace('Require Import PTree.Prob.Interface.Measure.',
        'Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.AE.')
    assert sources[COUPLING].startswith(prefix), 'Existing coupling capabilities changed'
    tail = without_comments(sources[COUPLING][len(prefix):])
    assert re.findall(r'\bLemma (\w+)',tail) == ['coupling_ae_implies_ae_lift']
    assert not re.search(r'\b(?:Instance|Existing|Hint|Axiom|Parameter|Admitted|Class)\b',tail)
    assert 'sem_lift_ae_restrict' in tail and 'sem_lift_refl' in tail
    assert sources['theories/PTreeFacts.v'] == frozen('theories/PTreeFacts.v').replace(
        'ProbabilisticTrace Bind.', 'ProbabilisticTrace Bind Algebra.')
    s = sources[OLD_CLIENT]
    a = s.index('(** Pin this regression');b = s.index('(** Regression: all three monad equations')
    assert s[:a]+s[b:] == frozen(OLD_CLIENT), 'Existing EnumQ regression changed'
    inserted = without_comments(s[a:b])
    assert inserted.count('#[local] Instance') == 2
    assert re.findall(r'Proof\.(.*?)Qed\.',inserted,re.S) == [
        ' apply peutt_bind_Proper. ', ' apply peutt_fmap_Proper. ']
    for p, names in [(PUBLIC,PUBLIC_NAMES),(DIRECT,DIRECT_NAMES)]:
        prefix = frozen(p)
        if p == PUBLIC:
            prefix = prefix.replace('From PTree.Eq.Backend Require Import SubEnumQ.',
                'From PTree.Eq.Backend Require Import SubEnumQ.\nFrom Coq Require Import Morphisms.')
        assert sources[p].startswith(prefix), 'Old regression changed: '+p
        tail = without_comments(sources[p][len(prefix):])
        assert re.findall(r'\bExample (\w+)',tail) == names
        assert tail.count('setoid_rewrite H.') == 2
        assert tail.count('setoid_rewrite Hpoint.') == 1
        assert not re.search(r'\b(?:Instance|Existing|Hint|Axiom|Parameter|Admitted)\b',tail)
    old_imports = set(frozen(ALL).splitlines())
    new_imports = set(sources[ALL].splitlines())
    assert new_imports - old_imports == {'Require PTree.Eq.Algebra.',
        'Require PTree.Regression.Semantics.GenericAlgebra.'}
    assert not old_imports - new_imports
    alg = without_comments(sources[ALG])
    assert not re.search(r'\b(?:FreeOmega|MathComp\w*|Axiom|Parameter|Admitted|Class|Hint|Existing)\b',alg)
    assert re.findall(r'\bInstance (\w+)',alg) == ['peutt_bind_Proper','peutt_fmap_Proper']
    # Same semantic profile as generic bind, no native or conclusion-level law.
    context = alg.split('Context ',1)[1].split('\n\n',1)[0]
    bind_context = without_comments(sources['theories/Eq/Bind.v']).split('Context ',1)[1].split('\n\n',1)[0]
    assert code(context) == code(bind_context), 'Unexpected Proper capability profile'
    assert alg.count('eapply peutt_bind with (RR := eq).') == 2
    from audit_behavior_routing import structural_check, STRUCTURAL, frozen as foundation
    from public_module_migration import registry_check
    internal=structural_check(foundation(STRUCTURAL),sources[STRUCTURAL]);registry_check(sources,internal)
    print(f'{len(old-CHANGED)} old modules frozen; exact Dirac relocation and six retained algebra equations checked.')

def manifest_check():
    before=json.loads(frozen('docs/CONTRACTS.json'))
    after=json.loads((ROOT/'docs/CONTRACTS.json').read_text())
    current={e['name']:e for e in after['endpoints']}
    assert len(current)==len(before['endpoints'])==465
    assert after['modules'] == sorted(set(before['modules'])|{'PTree.Eq.Algebra'})
    for group in ['api','soundness','capability']:
        assert after[group] == [RELOCATION.get(n,n) for n in before[group]],group
    changes=[]
    for e in before['endpoints']:
        n=RELOCATION.get(e['name'],e['name']);a=current[n]
        if e['name'] not in RELOCATION:
            assert e == a, 'Unapproved compiled contract change: '+n
        assert logical_axioms(a['assumptions']) <= logical_axioms(e['assumptions']),n
        if e != a:changes.append({'before':e,'after':a})
    assert json.loads((ROOT/'docs/GENERIC_ALGEBRA_CONTRACT_CHANGES.json').read_text()) == {
        'baseline':BASELINE,'changes':changes}
    before=json.loads(frozen('docs/MATHCOMP_DIRECT_CONTRACTS.json'))
    after=json.loads((ROOT/'docs/MATHCOMP_DIRECT_CONTRACTS.json').read_text())
    assert before['gate_m_modules']==after['gate_m_modules']
    current={e['name']:e for e in after['endpoints']}
    for e in before['endpoints']:assert e==current[e['name']],e['name']
    assert set(current)-{e['name'] for e in before['endpoints']} == {
        'PTree.Regression.Backend.MathCompDirect.'+n for n in DIRECT_NAMES}
    print('465 contracts preserved/generalized; all old Gate M contracts exactly preserved.')

def compiled_check():
    from audit_assumptions import check
    check()
    entries=query(ENDPOINTS)
    assert entries == json.loads((ROOT/'docs/GENERIC_ALGEBRA_CONTRACTS.json').read_text())['endpoints']
    by_name={e['name']:e for e in entries}
    for e in entries:
        assert logical_axioms(e['assumptions']) <= SOUNDNESS_AXIOMS,e['name']
        if e['name'] in CORE:
            assert not logical_axioms(e['assumptions']),e['name']
    for n in list(RELOCATION.values()):
        assert not re.search(r'FreeOmega|MathComp|Commutative|CountableAE|AELift',by_name[n]['type'])
    old={e['name']:e for e in json.loads(frozen('docs/CONTRACTS.json'))['endpoints']}
    for n in RELOCATION:
        short=n.rsplit('.',1)[1].replace('peutt_', 'free_omega_')
        e=by_name['PTree.Regression.Semantics.GenericAlgebra.'+short]
        assert code('\n'.join(e['type'].splitlines()[1:])) == code('\n'.join(old[n]['type'].splitlines()[1:])), short
        assert logical_axioms(e['assumptions']) <= logical_axioms(old[n]['assumptions']),short
    print('16 new compiled contracts; old FreeOmega Proper signatures recovered; no axiom growth.')

def kernel_check():
    modules=['Eq.Algebra','Eq.FreeOmega.Algebra','Prob.Interface.Coupling','Prob.FreeOmega.Measure',
      'Semantics.FreeOmega.MDPCoincidenceFreeOmega','PTreeFacts',
      'Regression.Semantics.GenericAlgebra','Regression.Infrastructure.PublicBehavior',
      'Regression.Infrastructure.AllImports']
    cmd=['opam','exec','--','coqchk','-silent','-R','_build/default/theories','PTree']
    for m in modules:cmd+=['-norec','PTree.'+m]
    subprocess.run(cmd,cwd=ROOT,check=True)
    print('9 safe module bodies checked jointly (-norec; dependencies trusted; Gate M excluded).')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--compiled',action='store_true');p.add_argument('--kernel',action='store_true')
    args=p.parse_args()
    check_source({p.relative_to(ROOT).as_posix():p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    manifest_check()
    if args.compiled:compiled_check()
    if args.kernel:kernel_check()
