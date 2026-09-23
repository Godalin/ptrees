#!/usr/bin/env python3
"""Generic bind extraction from 6e35c19; never weaken older frozen gates."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, without_comments, query, logical_axioms, SOUNDNESS_AXIOMS

BASELINE = '6e35c19'
NEW = {
    'theories/Eq/Bind.v', 'theories/Eq/BindScheduling.v',
    'theories/Prob/Interface/BindOrder.v', 'theories/Prob/FreeOmega/BindOrder.v',
    'theories/Prob/Backend/MathComp/BindOrder.v',
    'theories/Regression/Semantics/GenericBind.v'}
CHANGED = {
    'theories/Prob/Interface/Omega.v', 'theories/Eq/PEutt.v',
    'theories/Eq/FreeOmega/Bind.v', 'theories/Eq/Backend/MathComp/Direct.v',
    'theories/PTreeFacts.v', 'theories/Regression/Backend/MathCompDirect.v',
    'theories/Regression/Backend/SubEnumRBehavior.v',
    'theories/Regression/Infrastructure/AllImports.v',
    'theories/Regression/Infrastructure/ArchitectureBoundaries.v',
    'theories/Examples/BernoulliFactory/BernoulliFactoryComposition.v',
    'theories/Examples/InteractiveVonNeumann/InteractiveVonNeumannService.v'}
TYPE_CHANGES = {
    'PTree.Eq.PEutt.peutt_bind_cofinal',
    'PTree.Eq.PEutt.peutt_coinduction_upto_bind',
    'PTree.Eq.PEutt.stable_hitting_front_choice',
    'PTree.Eq.FreeOmega.Bind.peutt_bind'}
OLD_BIND = 'PTree.Eq.FreeOmega.Bind.peutt_bind'
NEW_BIND = 'PTree.Eq.Bind.peutt_bind'
CORE = ['PTree.Eq.Bind.peutt_bind', 'PTree.Eq.PEutt.peutt_bind_cofinal',
    'PTree.Eq.BindScheduling.ptree_bind_global_le_diagonal',
    'PTree.Eq.BindScheduling.ptree_bind_split_le_global',
    'PTree.Eq.BindScheduling.ptree_bind_cofinal_all']
NATIVE = ['PTree.Prob.Backend.MathComp.BindOrder.'+n for n in [
    'MathCompNativeBindOrderLaws', 'MathCompNativeMixedBindOrderLaws',
    'MathCompNativeDirectedCofinalityLaws', 'MathCompNativeOmegaSelection']]
FREE = ['PTree.Prob.FreeOmega.BindOrder.'+n for n in [
    'FreeOmegaObservableBindOrderLaws', 'FreeOmegaObservableMixedBindOrderLaws',
    'FreeOmegaObservableDirectedCofinalityLaws', 'FreeOmegaObservableOmegaSelection']]
REGRESSION = ['PTree.Regression.Semantics.GenericBind.'+n for n in [
    'constant_lub_quotient_equal','constant_lub_not_approx_forward',
    'constant_lub_not_approx_backward','observable_equality_does_not_imply_order',
    'sampled_zero_quotient_equal','sampled_zero_not_approx_bottom',
    'generic_bind_endpoint','generic_scheduling_endpoint','free_omega_heterogeneous_bind']]

@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT,text=True)

def code(s):
    return ' '.join(without_comments(s).split())

def strip_imports(s):
    s = without_comments(s)
    s = re.sub(r'(?m)^(?:From [^\n]* Require|Require) (?:Import|Export)?[^\n]*\.\s*', '', s)
    return s

def mask_proof(s, name):
    match = re.search(r'\b(?:Lemma|Theorem|Corollary|Example) '+name+r'\b', s)
    assert match, 'Missing declaration: '+name
    start = match.start()
    a = s.index('Proof.', start); b = s.index('Qed.', a)+len('Qed.')
    return s[:a]+'Proof. AUDITED_REPLACEMENT. Qed.'+s[b:]

def check_source(sources):
    old = {p for p in subprocess.check_output(['git','ls-tree','-r','--name-only',BASELINE],
             cwd=ROOT,text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW, 'Unexpected module addition/deletion'
    for p in old - CHANGED:
        assert sources[p] == frozen(p), 'Unrelated source drift: '+p
    omega = 'theories/Prob/Interface/Omega.v'
    assert sources[omega].startswith(frozen(omega)), 'Existing omega interfaces changed'
    p = 'theories/Eq/PEutt.v'
    expected = frozen(p).replace(
        '    ptree_bind_cofinal (MF := MF) t k.\n\nLemma stable_hitting_front_choice',
        '    ptree_bind_cofinal (MF := MF) t k.\n\nContext `{FSelect : @SemanticOmegaSelection MF FI FO}.\n\nLemma stable_hitting_front_choice')
    assert mask_proof(expected,'stable_hitting_front_choice') == mask_proof(sources[p],'stable_hitting_front_choice')
    proof = sources[p].split('Lemma stable_hitting_front_choice',1)[1].split('Qed.',1)[0]
    assert 'sem_lub_choose' in proof and not re.search(r'\b(?:choice|cid|Axiom|Admitted)\b',proof)
    p = 'theories/Eq/FreeOmega/Bind.v'
    before = strip_imports(frozen(p)); after = strip_imports(sources[p])
    for n in ['ptree_bind_hitting_le_diagonal','ptree_bind_split_le_hitting','ptree_bind_cofinal_all']:
        before=mask_proof(before,n); after=mask_proof(after,n)
    before = re.sub(r'\bCorollary peutt_bind\b[\s\S]*?Qed\.', '', before, count=1)
    assert code(before)==code(after), 'FreeOmega mathematics changed beyond bind extraction'
    for p in CHANGED:
        if '/Examples/' in p:
            assert sources[p] == frozen(p).replace('FreeOmega.Bind.peutt_bind','PTree.Eq.Bind.peutt_bind'), p
    p='theories/Regression/Backend/SubEnumRBehavior.v'
    assert mask_proof(frozen(p),'real_behavioral_bind') == mask_proof(sources[p],'real_behavioral_bind')
    direct = without_comments(sources['theories/Eq/Backend/MathComp/Direct.v'])
    assert not re.search(r'\b(?:cid|choice|induction|cofix|bind_bisim_candidate|leq_gfp)\b',direct)
    assert 'Proof. apply peutt_bind. Qed.' in direct
    assert 'ptree_bind_cofinal_all' in direct
    for p in ['theories/Eq/Bind.v','theories/Eq/BindScheduling.v']:
        c = without_comments(sources[p])
        assert not re.search(r'\b(?:FreeOmega|MathComp\w*|choice|cid|Axiom|Admitted|PEuttBindLaws|sem_eq_le)\b',c), p
    prototype=without_comments(sources['theories/Eq/BindScheduling.v'])
    assert not re.search(r'\bClass\b|SemanticOmegaFubiniLaws|MixedMeasureOmegaLaws',prototype)
    assert prototype.count('Hypothesis ') == 5, 'Prototype must keep explicit probability hypotheses'
    owners=[p for p,s in sources.items() if re.search(r'\b(?:Theorem|Lemma|Corollary|Definition|Notation) peutt_bind\b',without_comments(s))]
    assert owners==['theories/Eq/Bind.v'], owners
    for p in NEW:
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit)\b',without_comments(sources[p])),p
    from audit_behavior_routing import structural_check, STRUCTURAL, frozen as foundation
    from public_module_migration import registry_check
    internal=structural_check(foundation(STRUCTURAL),sources[STRUCTURAL]);registry_check(sources,internal)
    print(f'{len(old-CHANGED)} old theory modules byte-for-byte frozen; approximation, quotient and routing unchanged.')

def manifest_check():
    before=json.loads(frozen('docs/CONTRACTS.json'))
    after=json.loads((ROOT/'docs/CONTRACTS.json').read_text())
    current={e['name']:e for e in after['endpoints']}
    assert len(current)==len(before['endpoints'])==465
    for group in ['api','soundness','capability']:
        assert set(after[group])=={NEW_BIND if n==OLD_BIND else n for n in before[group]},group
    changes=[]
    for e in before['endpoints']:
        n=NEW_BIND if e['name']==OLD_BIND else e['name']; a=current[n]
        if e['name'] not in TYPE_CHANGES:
            assert e['type']==a['type'], 'Unapproved signature drift: '+e['name']
        assert logical_axioms(a['assumptions']) <= logical_axioms(e['assumptions']), 'New logical dependency: '+n
        if e!=a:
            changes.append({'before':e,'after':a})
    ledger=json.loads((ROOT/'docs/GENERIC_BIND_CONTRACT_CHANGES.json').read_text())
    assert ledger=={'baseline':BASELINE,'changes':changes}
    print(f'465 previous contracts accounted for; {len(changes)} changes recorded; no per-endpoint axiom growth.')

def compiled_check():
    from audit_assumptions import check
    check()
    entries=query(CORE+NATIVE+FREE+REGRESSION)
    for e in entries:
        assert logical_axioms(e['assumptions']) <= SOUNDNESS_AXIOMS,e['name']
        if e['name'] in CORE:
            assert not logical_axioms(e['assumptions']), e['name']
            assert not re.search(r'FubiniLaws|MixedMeasureOmegaLaws|ClassicalChoice|MathComp|FreeOmega',e['type'])
    fo=next(e for e in entries if e['name'].endswith('free_omega_heterogeneous_bind'))
    assert not any('Choice' in n for n in logical_axioms(fo['assumptions']))
    old=next(e for e in json.loads(frozen('docs/CONTRACTS.json'))['endpoints']
             if e['name']==OLD_BIND)
    # The regression specializes the generic theorem to exactly the previous
    # FreeOmega profile. Only local binder names and printer whitespace differ.
    rename={'X':'R1','Y':'R2','t':'t1','u':'t2','k':'k1','h':'k2','x':'r1','y':'r2'}
    specialized='\n'.join(fo['type'].splitlines()[1:])
    specialized=re.sub(r'\b(?:X|Y|t|u|k|h|x|y)\b',lambda m:rename[m[0]],specialized)
    assert code(specialized)==code('\n'.join(old['type'].splitlines()[1:])), 'FreeOmega profile drift'
    assert logical_axioms(fo['assumptions'])<=logical_axioms(old['assumptions'])
    print(f'{len(entries)} generic/native/negative endpoints checked; generic bind and scheduling have no global axioms.')

def mathcomp_manifest_check():
    before=json.loads(frozen('docs/MATHCOMP_DIRECT_CONTRACTS.json'))
    after=json.loads((ROOT/'docs/MATHCOMP_DIRECT_CONTRACTS.json').read_text())
    assert before['gate_m_modules']==after['gate_m_modules'], 'Gate M boundary changed'
    old={e['name']:e for e in before['endpoints']}
    new={e['name']:e for e in after['endpoints']}
    prefix='PTree.Eq.Backend.MathComp.Direct.'
    assert set(old)-set(new)=={prefix+n for n in [
        'mathcomp_direct_approx_unfold','mathcomp_direct_global_le_diagonal',
        'mathcomp_direct_split_le_global']}
    assert set(new)-set(old)=={
        'PTree.Regression.Backend.MathCompDirect.direct_heterogeneous_bind'}
    for n in set(old)&set(new):
        b,a=old[n],new[n]
        if n not in {prefix+'mathcomp_direct_bind_cofinal',prefix+'mathcomp_direct_peutt_bind'}:
            assert b['type']==a['type'], 'Unexpected direct signature drift: '+n
        assert logical_axioms(a['assumptions'])<=logical_axioms(b['assumptions']),n
        assert a['session_collapsed_universes']==b['session_collapsed_universes'],n
        assert bool(a['unsafe_hierarchy'])==bool(b['unsafe_hierarchy']),n
        assert set(a['unsafe_hierarchy'])<=set(b['unsafe_hierarchy']),n
    changes=[{'before':old.get(n),'after':new.get(n)}
             for n in sorted(set(old)|set(new)) if old.get(n)!=new.get(n)]
    ledger=json.loads((ROOT/'docs/GENERIC_BIND_MATHCOMP_CHANGES.json').read_text())
    assert ledger=={'baseline':BASELINE,'changes':changes}
    print('MathComp removals/generalization accounted for; logical dependencies do not grow; Gate M remains unsafe.')

def kernel_check():
    modules=['Prob.Interface.BindOrder','Prob.Interface.Omega','Prob.FreeOmega.BindOrder',
      'Prob.Backend.MathComp.BindOrder','Eq.BindScheduling','Eq.PEutt','Eq.Bind',
      'Eq.FreeOmega.Bind','PTreeFacts','Regression.Semantics.GenericBind',
      'Regression.Infrastructure.PublicBehavior','Regression.Infrastructure.AllImports']
    cmd=['opam','exec','--','coqchk','-silent','-R','_build/default/theories','PTree']
    for m in modules:cmd+=['-norec','PTree.'+m]
    subprocess.run(cmd,cwd=ROOT,check=True)
    print('12 safe module bodies kernel-checked jointly (-norec; dependencies trusted; Gate M excluded).')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--compiled',action='store_true');p.add_argument('--kernel',action='store_true')
    args=p.parse_args()
    sources={p.relative_to(ROOT).as_posix():p.read_text() for p in (ROOT/'theories').rglob('*.v')}
    check_source(sources);manifest_check();mathcomp_manifest_check()
    if args.compiled:compiled_check()
    if args.kernel:kernel_check()
