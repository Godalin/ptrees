#!/usr/bin/env python3
"""Current compiled contracts, with explicit safe and unchecked query contexts.

No history access and no snapshot-update mode. Accepted snapshots are data,
not executable migration scripts. Every registered group runs in CI.
"""
from rocq_paths import LOADPATH, source_path
import argparse
import json
import re
import subprocess
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS
from audit_mathcomp import query_gate_m
from mathcomp_policy import GATE_M, safe_targets, check_build_flags

MANIFEST = ROOT / 'tools/data/CONTRACT_SUITES.json'
ALLIMPORTS = 'PTree.Tests.AllImports'
POLICY = ROOT / 'tools/data/CONTRACT_POLICY.json'


def check_manifest(data):
    """Validate named coverage, not historical endpoint counts."""
    available = {e['name'] for e in data['endpoints']}
    for scope in ['api', 'capability', 'soundness']:
        names = data[scope]
        assert names and len(names) == len(set(names)), 'Empty/duplicate scope: ' + scope
        assert set(names) <= available, 'Missing scoped endpoint: ' + scope
    assert set(data['capability']) <= set(data['api'])
    # Mainline exceptions do not widen the stricter external-soundness policy.
    for entry in data['endpoints']:
        if entry['name'] in data['soundness']:
            assert logical_axioms(entry['assumptions']) <= SOUNDNESS_AXIOMS, entry['name']
    for name in [
        'PTree.Prob.Backend.SubEnumQ.FreeOmega.Compatibility.free_omega_qlift_sound',
        'PTree.Prob.Backend.SubEnumQ.FreeOmega.Compatibility.free_omega_qlift_eq_sound',
        'PTree.Eq.Backend.StableHittingDomainSubEnumQ.stable_hitting_denotational_adequacy',
        'PTree.Prob.Backend.Common.DomainTransport.oval_bidual_coupled_nat',
    ]:
        assert name in data['soundness'], 'Missing final soundness contract: ' + name


def load_suites():
    data = json.loads(MANIFEST.read_text())
    assert data['version'] == 1
    groups = data['groups']
    assert len(groups) == len({g['id'] for g in groups}), 'Duplicate suite id'
    assert not {g['id'] for g in groups} & SEMANTIC_CHECKS.keys(), 'Duplicate compiled check id'
    referenced = set()
    fields = set()
    result = []
    for group in groups:
        assert group['context'] in {'owners', 'recorded', 'safe-joint', 'gate-m-joint', 'gate-m'}
        path = group['snapshot']
        assert path.startswith('tools/data/') and '..' not in path and path.endswith('CONTRACTS.json')
        referenced.add(path)
        field = group.get('field', 'endpoints')
        assert field in {'endpoints', 'direct'}
        assert (path, field) not in fields, 'Duplicate snapshot group'
        fields.add((path, field))
        snapshot = json.loads((ROOT / path).read_text())
        entries = snapshot[group.get('field', 'endpoints')]
        assert entries and len(entries) == len({e['name'] for e in entries}), group['id']
        if 'gate_m_modules' in snapshot:
            assert snapshot['gate_m_modules'] == sorted(GATE_M), 'Reviewed allowlist changed'
        if path == 'tools/data/CONTRACTS.json':
            check_manifest(snapshot)
        unsafe = group['context'].startswith('gate-m')
        for e in entries:
            assert set(e) == ({'name', 'type', 'assumptions', 'unsafe_hierarchy',
                              'session_collapsed_universes'} if unsafe else {'name', 'type', 'assumptions'})
            assert logical_axioms(e['assumptions']) <= SOUNDNESS_AXIOMS | set(
                data['axiom_exceptions'].get(e['name'], [])), e['name']
            module = e['name'].rsplit('.', 1)[0].removeprefix('PTree.').replace('.', '/')
            if unsafe:
                assert isinstance(e['session_collapsed_universes'], bool), e['name']
                assert bool(e['unsafe_hierarchy']) == (module in GATE_M), e['name']
                # Rocq omits the theory warning for axiom-free safe controls,
                # even in this unchecked session. Actual Gate M declarations
                # must still report both their unsafe flag and the warning.
                if not e['session_collapsed_universes']:
                    assert module not in GATE_M and not logical_axioms(e['assumptions']), e['name']
            else:
                assert module not in GATE_M, 'Unchecked endpoint in safe group: ' + e['name']
        result.append((group, snapshot, entries))
    # A newly added snapshot cannot silently be omitted from the runner.
    on_disk = {p.relative_to(ROOT).as_posix() for p in (ROOT / 'tools/data').glob('*CONTRACTS.json')}
    assert referenced == on_disk, ('Unregistered/missing snapshot', referenced ^ on_disk)
    for path in referenced:
        snapshot = json.loads((ROOT / path).read_text())
        assert {(path, k) for k in ['endpoints', 'direct'] if k in snapshot} <= fields, path
    contexts = {g['id']: g['context'] for g, _, _ in result}
    assert contexts['direct_iteration'] == contexts['iteration_algebra'] == 'safe-joint'
    assert contexts['contracts'] == 'recorded'
    names = {e['name'] for _, _, entries in result for e in entries}
    assert set(data['axiom_exceptions']) <= names
    for name in [
        'PTree.Eq.Bind.peutt_bind',
        'PTree.Prob.Backend.SubEnumQ.FreeOmega.Compatibility.free_omega_qlift_sound',
        'PTree.Eq.Backend.StableHittingDomainSubEnumQ.stable_hitting_denotational_adequacy',
        'PTree.Interp.IterationUniform.ptree_peutt_iteration_uniform',
        'PTree.Tests.Capabilities.PTreeUniformity.state_fold_into_ptree',
        'PTree.Tests.Capabilities.PTreeUniformity.exception_fold_into_ptree',
    ]:
        assert name in names, 'Missing maintained endpoint: ' + name
    return result


def check_group(group, snapshot, entries):
    context = group['context']
    names = [e['name'] for e in entries]
    if context.startswith('gate-m'):
        registered = json.loads(MANIFEST.read_text())['axiom_exceptions']
        exceptions = {n: registered[n] for n in names if n in registered}
        kwargs = {'axiom_exceptions': exceptions} if exceptions else {}
        actual = query_gate_m(names, joint=context == 'gate-m-joint', **kwargs)
    else:
        modules = [ALLIMPORTS] if context == 'safe-joint' else (
            snapshot['modules'] if context == 'recorded' else None)
        actual = query(names, modules)
    compare(entries, actual)
    print(f"{group['id']}: {len(entries)} exact type/assumption contracts ({context})", flush=True)


def check_protocol_boundary():
    """Retain the cause-sensitive negative test, separate from positive uniformity."""
    script = '''
Require Import PTree.Tests.AllImports.
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
    result = subprocess.run(['opam', 'exec', '--', 'coqtop', '-quiet',
        *LOADPATH], cwd=ROOT, input=script,
        text=True, capture_output=True)
    assert result.returncode == 0, result.stderr
    assert result.stdout.count('UNIFORM_BOUNDARY_START') == 1
    assert result.stdout.count('UNIFORM_BOUNDARY_END') == 1
    errors = result.stdout + result.stderr
    assert errors.count('Error:') == 1 and 'universe inconsistency' in errors.lower(), errors
    print('Old protocol package rejected specifically by universe inconsistency; direct package checked positively.')


def mathcomp_native_check():
    """Retained native mathematics, not a recursive behavioral backend."""
    groups = {
        'PTree.Prob.Backend.MathComp.Measure': [
            'MathCompNodeSemanticMeasure', 'MathCompNodeSemanticSubprobability',
            'MathCompNodeSemanticMeasureCoreLaws', 'MathCompNodeSemanticMeasureDiracAELaws',
            'MathCompNodeSemanticMeasureCouplingAELaws', 'MathCompNodeSemanticOmega'],
        'PTree.Prob.Backend.MathComp.NativeLaws': [
            'MathCompNativeMixedMeasure', 'MathCompNativeMixedMeasureUnitLaws',
            'MathCompNativeMixedMeasureNodeBindLaws', 'MathCompNativeTotalProperLaws',
            'mathcomp_native_zero_returned', 'mathcomp_native_le_refl',
            'mathcomp_native_le_trans', 'mathcomp_native_zero_le',
            'mathcomp_native_lub_constant', 'mathcomp_native_prefix_sup',
            'MathCompNativeCofinalityLaws', 'mathcomp_native_bind_le_k'],
        'PTree.Prob.Backend.MathComp.Coupling': ['mathcomp_coupling_realization'],
        'PTree.Prob.Backend.MathComp.OrderLaws': [
            'mathcomp_native_sintegral_le', 'mathcomp_native_integral_le',
            'mathcomp_native_bind_le_mu', 'mathcomp_native_le_antisym',
            'mathcomp_native_lub_upper', 'mathcomp_native_lub_least',
            'MathCompNativeOrderLaws'],
        'PTree.Examples.Probability.MathCompOrder': [
            'checked_native_order',
            'cemetery_mass_not_monotone', 'partial_sampling_returned_mass',
            'partial_sampling_bind_monotone'],
        'PTree.Prob.Backend.MathComp.OmegaLaws': [
            'mathcomp_native_lub', 'mathcomp_native_lub_spec',
            'mathcomp_native_sintegral_cvg', 'mathcomp_native_integral_lub',
            'mathcomp_native_bind_lub', 'MathCompNativeOmegaLaws',
            'mathcomp_native_bind_lub_k', 'mathcomp_native_bind_ae_eq',
            'mathcomp_native_bind_lub_ae', 'mathcomp_native_bind_zero',
            'MathCompNativeMixedOmegaLaws', 'mathcomp_native_double_diagonal',
            'MathCompNativeFubiniLaws', 'mathcomp_native_bind_diagonal',
            'MathCompNativeDiagonalLaws', 'mathcomp_native_ae_zero',
            'mathcomp_native_ae_lub', 'MathCompNativeOmegaAELaws',
            'mathcomp_native_lub_cofinal'],
        'PTree.Prob.Backend.MathComp.BindLaws': [
            'mathcomp_joint_bind', 'mathcomp_joint_bindE',
            'mathcomp_joint_integral_projection', 'mathcomp_native_bind_zero_left',
            'mathcomp_native_eq_le', 'mathcomp_native_le_eq_r', 'mathcomp_native_le_eq_l',
            'mathcomp_native_eq_Equivalence', 'mathcomp_native_le_Proper',
            'mathcomp_native_bind_Proper', 'mathcomp_native_lift_bind',
            'MathCompNativeBindLaws', 'MathCompNativeMixedLaws'],
        'PTree.Prob.Backend.MathComp.Retry': [
            'mathcomp_root_finite', 'mathcomp_retry_fixed_point'],
        'PTree.Examples.Probability.MathCompOmega': [
            'checked_omega', 'checked_mixed_omega', 'checked_diagonal',
            'checked_fubini', 'checked_bind', 'checked_mixed', 'checked_omega_ae',
            'null_branches_need_no_continuity',
            'relation_survives_kernel_bind'],
        'PTree.Examples.BernoulliFactory.RealBernoulliMathComp': [
            'mathcomp_binary_oracle_lub', 'mathcomp_binary_oracle_is_ast'],
        'PTree.Tests.Imports.MathCompUniverse': ['self_nested_sampling'],
    }
    entries = query([module+'.'+name for module, names in groups.items() for name in names])
    for e in entries:
        assert logical_axioms(e['assumptions']) <= SOUNDNESS_AXIOMS, e['name']
        assert not re.search(r'\b(?:FreeOmega\w*|free_omega_\w*|peutt|stable_head)\b', e['type']), e['name']
        if '.MathComp.OrderLaws.' in e['name'] or '.Backend.MathCompOrder.' in e['name']:
            assert 'MathCompCouplingGluing' not in e['type'], 'Order must not assume gluing'
            if not e['name'].endswith(('MathCompNativeOrderLaws', 'checked_native_order')):
                assert not re.search(r'\bSemantic\w*Laws\b', e['type']), 'Native math must not assume the desired law'
        if any(part in e['name'] for part in [
                '.MathComp.OmegaLaws.', '.MathComp.BindLaws.', '.MathComp.Retry.',
                '.Backend.MathCompOmega.']):
            assert 'MathCompCouplingGluing' not in e['type'], 'Native continuity/bind must not assume gluing'
            # Instance endpoints conclude a capability; mathematical lemmas
            # must not receive any capability or provided transport witness.
            short = e['name'].rsplit('.', 1)[-1]
            if not short.startswith(('MathCompNative', 'checked_')):
                assert not re.search(r'\bSemantic\w*Laws\b', e['type']), 'Native math assumes its desired law'
    print(f'{len(entries)} native MathComp endpoints checked; no completion/frontier in signatures; unchanged logical whitelist.')


def real_joint_check():
    """Concrete realization strengthening; keep frozen DS signatures intact."""
    groups = {
        'PTree.Prob.Backend.SubEnumR.FreeOmega.CountableSupport': [
            'subenumR_free_omega_enumerate', 'subenumR_free_omega_enumerate_covers',
            'subenumR_free_omega_model_enumerated', 'subenumR_free_omega_model_countable'],
        'PTree.Prob.Backend.SubEnumR.FreeOmega.JointRealization': [
            'subenumR_qlift_sound', 'subenumR_qlift_joint_mass_support',
            'subenumR_qlift_eq_sound_via_joint'],
    }
    policy = json.loads(POLICY.read_text())
    groups['PTree.Examples.Validation.SubEnumRJointRealization'] = policy['clients'][
        'theories/Examples/Validation/SubEnumRJointRealization.v']
    entries = query([module+'.'+name for module, names in groups.items() for name in names])
    for e in entries:
        assert logical_axioms(e['assumptions']) <= SOUNDNESS_AXIOMS, e['name']
        assert not re.search(r'\b(?:Semantic\w*Laws|ExternalJointRealization)\b', e['type']), e['name']
        if e['name'].endswith('.subenumR_free_omega_enumerate_covers'):
            assert 'free_omega_modelable' not in e['type'], 'Raw cover must not require validity'
        if e['name'].endswith('.subenumR_qlift_sound'):
            assert all(s in e['type'] for s in ['free_omega_modelable', 'free_omega_qlift', 'oval_coupled'])
    print(f'{len(entries)} finite-real countable/joint/regression endpoints checked; unchanged logical whitelist.')


def generic_quotient_check():
    """New native-parametric bridge; do not regenerate frozen DS snapshots."""
    groups = {
        'PTree.Prob.FreeOmega.Validation.Continuity': [
            'model_upper_continuous', 'model_native_continuous_ae',
            'model_sample_lub', 'model_bind_lub'],
        'PTree.Prob.FreeOmega.Validation.Observation': ['model_observes_upper'],
        'PTree.Prob.FreeOmega.Validation.Relational': ['model_upper_rel_comp'],
        'PTree.Prob.FreeOmega.Validation.Quotient': [
            'model_qlift_bidual_raw', 'model_qlift_bidual', 'model_qlift_upper',
            'model_qlift_upper_mass', 'model_qlift_eq_upper',
            'model_qlift_eq_modelable', 'model_qlift_eq_sound'],
        'PTree.Prob.Backend.SubEnumR.FreeOmega.Validation': [
            'subenumR_native_model_lub', 'subenumR_qlift_bidual_raw',
            'subenumR_qlift_bidual', 'subenumR_qlift_eq_modelable'],
        'PTree.Prob.Backend.SubEnumQ.FreeOmega.Validation': [
            'subenumQ_native_model_lub', 'subenumQ_qlift_bidual_raw',
            'subenumQ_generic_qlift_bidual', 'subenumQ_qlift_eq_upper',
            'subenumQ_qlift_eq_modelable', 'subenumQ_qlift_eq_sound'],
        'PTree.Prob.Backend.SubEnumQ.FreeOmega.CountableSupport': [
            'subenumQ_free_omega_model_enumerated', 'subenumQ_free_omega_model_countable'],
        'PTree.Prob.Backend.SubEnumQ.FreeOmega.JointRealization': [
            'subenumQ_qlift_sound', 'subenumQ_qlift_eq_sound_via_joint',
            'subenumQ_qlift_joint_mass_support'],
        'PTree.Examples.Validation.GenericFreeOmegaValidation': [
            'generic_q_joint_without_legacy'],
        'PTree.Prob.Backend.SubEnumQ.FreeOmega.Compatibility': ['subenumQ_generic_qlift_tests'],
    }
    policy = json.loads(POLICY.read_text())
    path = 'theories/Examples/Validation/GenericQuotientValidation.v'
    groups['PTree.Examples.Validation.GenericQuotientValidation'] = policy['clients'][path]
    entries = query([module+'.'+name for module, names in groups.items() for name in names])
    for e in entries:
        assert logical_axioms(e['assumptions']) <= SOUNDNESS_AXIOMS, e['name']
        if e['name'].startswith('PTree.Prob.FreeOmega.Validation.'):
            assert not re.search(r'\b(?:SubEnumQ\w*|ptree|SemanticOmegaLaws|SemanticMeasureBindLaws)\b', e['type']), e['name']
        if e['name'].endswith('.model_qlift_bidual_raw'):
            assert 'free_omega_modelable' not in e['type'], 'Raw bridge must allow invalid middle terms'
    print(f'{len(entries)} generic quotient/adapter/regression endpoints checked; unchanged logical whitelist.')


def stable_hitting_validation_check():
    """One generic validity proof, fully discharged Q/R specializations."""
    groups = {
        'PTree.Prob.FreeOmega.Validation.StableHitting': [
            'ptree_hitting_model_commutation', 'ptree_hitting_approx_modelable',
            'ptree_hitting_approx_model_increasing', 'ptree_canonical_hitting_spec',
            'ptree_canonical_hitting_modelable', 'ptree_canonical_hitting_denotes',
            'stable_hitting_modelable', 'stable_hitting_denotational_adequacy',
            'stable_hitting_model_eq', 'stable_hitting_model_mass_lub'],
        'PTree.Eq.Backend.StableHittingDomainSubEnumQ': [
            'subenumQ_stable_hitting_modelable', 'subenumQ_stable_hitting_denotational_adequacy'],
        'PTree.Eq.Backend.StableHittingDomainSubEnumR': [
            'subenumR_stable_hitting_modelable', 'subenumR_stable_hitting_denotational_adequacy',
            'subenumR_stable_hitting_domain_eq', 'subenumR_stable_hitting_mass_lub'],
        'PTree.Prob.Backend.SubEnumQ.FreeOmega.CountableSupport': ['subenumQ_free_omega_model_countable'],
        'PTree.Prob.Backend.SubEnumQ.FreeOmega.JointRealization': ['subenumQ_qlift_sound'],
    }
    policy = json.loads(POLICY.read_text())
    groups['PTree.Examples.Validation.StableHittingDomain'] = policy['clients'][
        'theories/Examples/Validation/StableHittingDomain.v']
    entries = query([module+'.'+name for module, names in groups.items() for name in names])
    for e in entries:
        assert logical_axioms(e['assumptions']) <= SOUNDNESS_AXIOMS, e['name']
        if '.Validation.StableHitting.' in e['name']:
            assert not re.search(r'\b(?:SubEnumQ\w*|SubEnumR\w*|MathComp\w*)\b', e['type']), e['name']
            assert not re.search(r'\b(?:SemanticOmegaLaws|SemanticMeasureBindLaws)\b', e['type']), e['name']
        if '.Eq.Backend.' in e['name'] or '.Examples.' in e['name'] or '.Tests.' in e['name']:
            assert not re.search(r'\b(?:Semantic\w*Laws|native_ae|native_lub|no_event)\b', e['type']), e['name']
        if e['name'].endswith(('.subenumQ_stable_hitting_modelable', '.subenumR_stable_hitting_modelable')):
            assert e['type'].count('free_omega_modelable') == 1, 'Validity must be a conclusion, not a premise'
    print(f'{len(entries)} generic hitting/Q/R/realization endpoints checked; unchanged logical whitelist.')


# Extra mathematical constraints are not exact snapshots. Keep their predicates
# explicit, alongside the sole compiled runner, rather than invent a schema for
# arbitrary type restrictions. Each runs in its own safe owner context.
SEMANTIC_CHECKS = {
    'mathcomp-native': mathcomp_native_check,
    'real-joint': real_joint_check,
    'generic-quotient': generic_quotient_check,
    'stable-hitting': stable_hitting_validation_check,
}


def run_checks(suites, gate, group=None):
    known = {g['id'] for g, _, _ in suites}
    assert not known & SEMANTIC_CHECKS.keys(), 'Duplicate compiled check id'
    if group:
        assert group in known | SEMANTIC_CHECKS.keys(), 'Unknown group: ' + group
        selected_gate = next(('M' if g['context'].startswith('gate-m') else 'S'
                              for g, _, _ in suites if g['id'] == group), 'S')
        assert gate in ['all', selected_gate], 'Group excluded by --gate: ' + group
    for g, d, es in suites:
        selected_gate = 'M' if g['context'].startswith('gate-m') else 'S'
        if gate in ['all', selected_gate] and (not group or g['id'] == group):
            check_group(g, d, es)
    if gate != 'M':
        if not group:
            check_protocol_boundary()
        for name, check in SEMANTIC_CHECKS.items():
            if not group or group == name:
                check()


def build_targets(gate):
    """Safe-only builds remain available without loading Gate M."""
    check_build_flags(ROOT)
    safe = safe_targets(ROOT) if gate in ['S', 'all'] else []
    unsafe = [str(source_path(m).relative_to(ROOT).with_suffix('.vo'))
              for m in sorted(GATE_M)] if gate in ['M', 'all'] else []
    subprocess.run(['opam', 'exec', '--', 'dune', 'build', *safe, *unsafe],
                   cwd=ROOT, check=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--metadata-only', action='store_true')
    parser.add_argument('--gate', choices=['S', 'M', 'all'], default='all')
    parser.add_argument('--group', help='Snapshot suite id or ' + ', '.join(SEMANTIC_CHECKS))
    parser.add_argument('--build', action='store_true', help='Build selected trust domain before checking')
    args = parser.parse_args()
    suites = load_suites()
    known = {g['id'] for g, _, _ in suites} | SEMANTIC_CHECKS.keys()
    if args.group and args.group not in known:
        parser.error('Unknown group: ' + args.group)
    if args.metadata_only and args.build:
        parser.error('--metadata-only does not build')
    print(f'{len(suites)} snapshot groups + {len(SEMANTIC_CHECKS)} mathematical checks; no Git history required.', flush=True)
    if args.build:
        build_targets(args.gate)
    if not args.metadata_only:
        run_checks(suites, args.gate, args.group)
