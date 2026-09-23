#!/usr/bin/env python3
"""Consumer convergence from c2dea6b; no foundational interface changes."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = 'c2dea6b'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
DIRECT = 'theories/Regression/Backend/MathCompDirect.v'
REL = 'theories/Eq/FreeOmega/Relation.v'
ITER = 'theories/Eq/FreeOmega/Iter.v'
BASE = 'theories/Interp/FreeOmega/Base.v'
GUARD = 'theories/Interp/FreeOmega/Guarded.v'
COFINAL = 'theories/Interp/FreeOmega/Cofinality.v'
NEW = {'theories/'+p+'.v' for p in [
    'Prob/FreeOmega/RelationalLimit', 'Eq/Iter', 'Interp/Scheduling',
    'Interp/Preservation', 'Interp/Guarded', 'Regression/Semantics/GenericConsumers']}
CHANGED = {ALL, DIRECT, REL, ITER, BASE, GUARD, COFINAL, 'theories/PTreeFacts.v'}
RELOCATION = {'PTree.Eq.FreeOmega.Iter.peutt_iter_eventful_of_generator_closed':
              'PTree.Eq.Iter.peutt_iter_eventful_of_generator_closed'}
ENDPOINTS = ['PTree.'+m+'.'+n for m, names in {
    'Prob.FreeOmega.RelationalLimit': ['free_omega_lift_lub'],
    'Eq.Iter': ['iter_eventful_bisim_candidate', 'iter_eventful_generator_closed',
                'peutt_iter_eventful_of_generator_closed'],
    'Interp.Scheduling': ['ptree_interp_hitting_le_diagonal', 'ptree_interp_split_le_hitting',
                         'ptree_interp_cofinal_all'],
    'Interp.Preservation': ['interp_bisim_candidate', 'interp_vis_fusion',
                           'peutt_interp_of_vis_fusion', 'interp_generator_closed',
                           'peutt_interp_of_generator_closed'],
    'Interp.Guarded': ['stable_head_is_visible', 'guarded_handler', 'guarded_handler_of_hitting',
                      'guarded_handler_vis_fusion', 'peutt_interp_guarded', 'peutt_interp_guarded_Proper'],
    'Regression.Semantics.GenericConsumers': ['generic_eventful_iter', 'free_omega_eventful_iter',
        'generic_guarded_contract', 'generic_guarded_interp', 'generic_interp_schedule', 'real_guarded_interp'],
}.items() for n in names]

@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT,text=True)

def proof_replace(s, name, proof):
    start = re.search(r'\b(?:Lemma|Theorem|Corollary) '+name+r'\b', s)
    assert start, name
    a=s.index('Proof.',start.start()); b=s.index('Qed.',a)+4
    return s[:a]+proof+s[b:]

def definition_replace(s, name, definition):
    a=s.index('Definition '+name); b=s.index('\n\n',a)
    return s[:a]+definition+s[b:]

def guard_expected():
    s=frozen(GUARD).replace('From PTree.Interp.FreeOmega Require Import Base.',
        'From PTree.Interp.FreeOmega Require Import Base.\nFrom PTree.Interp Require Export Guarded.')
    a=s.index('(** Semantic visible guarding:'); b=s.index('Section GuardedInterp.',a)
    s=s[:a]+'''(** Canonical completion specializations of the generic guarded theory.
    These keep the established native capability contract; no proof is copied. *)
'''+s[b:]
    s=definition_replace(s,'guarded_handler','''Definition guarded_handler : Prop :=
  @Guarded.guarded_handler E F MN MF FI FreeOmegaMixedMeasure FO handler.''')
    for n,h in [('guarded_handler_of_hitting','H'),('guarded_handler_vis_fusion','Hguard'),
                ('peutt_interp_guarded','Hguard')]:
        s=proof_replace(s,n,f'Proof. apply Guarded.{n}. exact {h}. Qed.')
    return s

def base_expected():
    s=frozen(BASE).replace('From PTree.Interp.FreeOmega Require Import Cofinality.',
        'From PTree.Interp.FreeOmega Require Import Cofinality.\nRequire PTree.Interp.Preservation.')
    fi='(FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))'
    fc='(FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NC := NC) (NO := NO))'
    fo='(FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO))'
    profile=f'E F MN MF {fi} {fc} FreeOmegaMixedMeasure {fo} A B RR handler'
    s=definition_replace(s,'interp_bisim_candidate',
        "Definition interp_bisim_candidate\n    (s1 : ptree' F MN A) (s2 : ptree' F MN B) : Prop :=\n"
        '  @Preservation.interp_bisim_candidate '+profile+' s1 s2.')
    for n in ['interp_vis_fusion','interp_generator_closed']:
        s=definition_replace(s,n,f'Definition {n} : Prop :=\n  @Preservation.{n} {profile}.')
    for n,h in [('peutt_interp_of_vis_fusion','Hvis'),('peutt_interp_of_generator_closed','Hclosed')]:
        s=proof_replace(s,n,f'Proof. apply Preservation.{n}. exact {h}. Qed.')
    return s

def cofinal_expected():
    s=frozen(COFINAL).replace('Require Import PTree.Interp.Kernel.',
        'Require Import PTree.Interp.Kernel.\nRequire PTree.Interp.Scheduling.')
    fi='(FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))'
    fo='(FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO))'
    for n,tail in [('ptree_interp_hitting_le_diagonal','R fuel t'),
                   ('ptree_interp_split_le_hitting','R source_fuel head_fuel t'),
                   ('ptree_interp_cofinal_all','R t')]:
        args='_ _ _ _' if n.endswith('cofinal_all') else '_ _ _'
        s=proof_replace(s,n,f'''Proof.
  exact (@Scheduling.{n} E F MN MF
    {fi} FreeOmegaMixedMeasure {fo}
    {args} handler {tail}).
Qed.''')
    return s

def check_source(sources):
    old={p for p in subprocess.check_output(['git','ls-tree','-r','--name-only',BASELINE],
        cwd=ROOT,text=True).splitlines() if p.endswith('.v')}
    assert set(sources)==old|NEW, 'Unexpected module addition/deletion'
    for p in old-CHANGED:
        assert sources[p]==frozen(p), 'Unrelated source drift: '+p
    s=frozen(REL).replace('From PTree.Eq Require Import StableHittingRelation.',
        'From PTree.Eq Require Import StableHittingRelation.\nFrom PTree.Prob.FreeOmega Require Import RelationalLimit.')
    for kind in ['pstruct','pstrong']:
        a=s.index('    + unfold stable_hitting in Hout1, Hout2.')
        b=s.index('    + intros h1 h2 Hhead.',a)
        s=s[:a]+'''    + eapply free_omega_lift_lub; [exact Hout1|exact Hout2|].
      intro fuel. apply FOQLStructural.
      exact (ptree_hitting_'''+kind+''' (RR := RR) fuel Hs).
'''+s[b:]
    assert sources[REL]==s, 'Structural bridge changed beyond limit extraction'
    s=frozen(ITER);a=s.index('Section EventfulBehavioralIterationClosure.')
    b=s.index('End EventfulBehavioralIterationClosure.')+len('End EventfulBehavioralIterationClosure.')
    assert sources[ITER]=='From PTree.Eq Require Export Iter.\n'+s[:a]+s[b:]
    assert sources[BASE]==base_expected(), 'Interpreter base specialization drift'
    assert sources[GUARD]==guard_expected(), 'Guard specialization drift'
    assert sources[COFINAL]==cofinal_expected(), 'Cofinality specialization drift'
    assert sources['theories/PTreeFacts.v']==frozen('theories/PTreeFacts.v').replace(
        'ProbabilisticTrace Bind Algebra.','ProbabilisticTrace Bind Algebra Iter.').replace(
        'From PTree.Interp.FreeOmega Require Export Guarded Atomic MDP.',
        'From PTree.Interp Require Export Guarded.\nFrom PTree.Interp.FreeOmega Require Export Atomic MDP.')
    assert sources[DIRECT].startswith(frozen(DIRECT)), 'Old Gate M proof changed'
    tail=without_comments(sources[DIRECT][len(frozen(DIRECT)):])
    assert re.findall(r'\b(?:Example|Lemma|Definition) (\w+)',tail)==[
        'direct_eventful_iter','direct_guarded_handler','direct_handler_guarded',
        'direct_guarded_interp','direct_guarded_tau']
    oldlines=frozen(ALL).splitlines()
    additions=['Require PTree.'+p.removeprefix('theories/').removesuffix('.v').replace('/','.')+'.' for p in NEW]
    assert sources[ALL]=='\n'.join(oldlines[:2]+sorted(oldlines[2:]+additions))+'\n'
    for p in NEW:
        c=without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|Class|Hint|CoFixpoint)\b|Unset .*Checking',c),p
        if p.startswith(('theories/Eq/','theories/Interp/')):
            assert not re.search(r'FreeOmega|MathComp|SubEnum|FOQL|free_omega|sem_eq_le',c),p
            assert '#[global]' not in c,p
    assert 'FOQLLub' in sources['theories/Prob/FreeOmega/RelationalLimit.v']
    # Preserve the exact generic iteration proof, not a backend copy.
    oldproof=re.search(r'Theorem peutt_iter_eventful_of_generator_closed.*?(Proof\..*?Qed\.)',
                       frozen(ITER),re.S).group(1)
    assert oldproof in sources['theories/Eq/Iter.v']
    print(f'{len(old-CHANGED)} old modules byte-frozen; exact consumer extraction/specialization checked.')

def compiled_check():
    before=json.loads(frozen('docs/CONTRACTS.json'))
    after=json.loads((ROOT/'docs/CONTRACTS.json').read_text())
    assert len(before['endpoints'])==len(after['endpoints'])==465
    for key in ['api','soundness','capability']:
        assert after[key]==[RELOCATION.get(n,n) for n in before[key]],key
    current={e['name']:e for e in after['endpoints']}
    changes=[]
    for b in before['endpoints']:
        a=current[RELOCATION.get(b['name'],b['name'])]
        assert logical_axioms(a['assumptions']) <= logical_axioms(b['assumptions']),a['name']
        if b['name'] not in RELOCATION:
            assert a==b, 'Unapproved old contract change: '+b['name']
        if a!=b: changes.append({'before':b,'after':a})
    assert {'baseline':BASELINE,'changes':changes}==json.loads(
        (ROOT/'docs/GENERIC_CONSUMER_CONTRACT_CHANGES.json').read_text())
    entries=query(ENDPOINTS)
    assert entries==json.loads((ROOT/'docs/GENERIC_CONSUMER_CONTRACTS.json').read_text())['endpoints']
    for e in entries:
        assert logical_axioms(e['assumptions'])<=SOUNDNESS_AXIOMS,e['name']
        if e['name'].startswith(('PTree.Eq.Iter.','PTree.Interp.')):
            assert not logical_axioms(e['assumptions']),e['name']
            assert not re.search(r'FreeOmega|MathComp|SubEnum',e['type']),e['name']
    from audit_assumptions import check
    check()
    old_direct=json.loads(frozen('docs/MATHCOMP_DIRECT_CONTRACTS.json'))
    new_direct=json.loads((ROOT/'docs/MATHCOMP_DIRECT_CONTRACTS.json').read_text())
    assert old_direct['gate_m_modules']==new_direct['gate_m_modules']
    direct={e['name']:e for e in new_direct['endpoints']}
    for e in old_direct['endpoints']:assert direct[e['name']]==e,e['name']
    assert set(direct)-{e['name'] for e in old_direct['endpoints']}=={
        'PTree.Regression.Backend.MathCompDirect.'+n for n in [
            'direct_eventful_iter','direct_handler_guarded','direct_guarded_interp','direct_guarded_tau']}
    print('All 465 contracts checked; explicit change ledger; generic consumers have no global axioms.')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--compiled',action='store_true')
    args=p.parse_args()
    check_source({p.relative_to(ROOT).as_posix():p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:compiled_check()
