#!/usr/bin/env python3
"""Long-term source and compiled probability-soundness safety contracts."""
import argparse
import json
import re
from audit_assumptions import ROOT, MANIFEST, check, without_comments, query, logical_axioms, SOUNDNESS_AXIOMS
from audit_architecture import graph

POLICY = ROOT / 'docs/CONTRACT_POLICY.json'


def code_only(text):
    # Strings in error messages and notation are not proof commands.
    return re.sub(r'"(?:""|[^"\n])*"', '""', without_comments(text))


def classes(text):
    code = code_only(text)
    result = {}
    for match in re.finditer(r'\bClass\s+(\w+)', code):
        end = re.search(r'\.(?=\s|$)', code[match.start():])
        assert end, 'Unrecognized class declaration: ' + match.group(1)
        assert match.group(1) not in result, 'Duplicate class name'
        result[match.group(1)] = ' '.join(code[match.start():match.start()+end.end()].split())
    return result


def independent_math(sources):
    """Keep the actual external mathematics independent, not only its signatures."""
    forbidden = r'\b(?:FreeOmega|free_omega_\w+|Semantic\w+|ptree|SubEnum)\b'
    for path, text in sources.items():
        if path.startswith('theories/Prob/Domain/'):
            assert not re.search(forbidden, code_only(text)), 'Domain is not independent: ' + path
    for name in ['RealTransport', 'CountableRealTransport', 'DomainTransport', 'CountableCoupling']:
        code = code_only(sources['theories/Prob/Backend/Common/' + name + '.v'])
        assert not re.search(forbidden, code), 'Transport mathematics imports program semantics: ' + name
        if name in ['RealTransport', 'CountableRealTransport']:
            assert not re.search(r'\bOmegaVal\b', code), 'Scalar transport depends on the domain'
    hitting = code_only(sources['theories/Eq/Backend/StableHittingDomainSubEnum.v'])
    for start, end in [('Section DomainKernel.', 'End DomainKernel.'),
                       ('Definition ptree_domain_kernel', 'Definition ptree_domain_approx')]:
        assert start in hitting and end in hitting, 'Missing independent kernel block'
        block = hitting.split(start, 1)[1].split(end, 1)[0]
        assert not re.search(r'\b(?:FreeOmega|free_omega_\w+|stable_hitting_approx|ptree_hitting_approx|sem_\w+)\b', block), \
            'Mathematical kernel must not be defined using formal iterates'


def source_check(sources=None, policy=None):
    if sources is None:
        sources = {p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')}
    policy = policy or json.loads(POLICY.read_text())
    found_classes = {}
    for path, text in sources.items():
        code = code_only(text)
        assert not re.search(r'\b(?:Admitted|admit|Axiom|Axioms|Parameter|Parameters)\b', code), \
            'Unfinished proof or semantic assumption: ' + path
        assert not re.search(r'\bUnset\s+Universe\s+Checking\b', code), \
            'Unsafe universe setting in maintained theory: ' + path
        for name, decl in classes(text).items():
            found_classes[path + ':' + name] = decl
    assert found_classes == policy['classes'], 'Capability declaration drift (new or changed Class)'
    independent_math(sources)
    for path, names in policy['regressions'].items():
        assert path in sources, 'Missing regression module: ' + path
        code = code_only(sources[path])
        for name in names:
            assert re.search(r'\b(?:Example|Lemma|Theorem)\s+'+re.escape(name)+r'\b',code), \
                'Missing regression: ' + name
    joint = code_only(sources['theories/Prob/Backend/SubEnum/FreeOmega/JointSoundness.v'])
    assert 'free_omega_qlift_countable_constraints' in joint and 'oval_bidual_coupled' in joint
    assert not re.search(r'\b(?:induction|elim|FOQLComp)\b', joint), 'Final bridge must not require intermediate validity'
    hitting = code_only(sources['theories/Eq/Backend/StableHittingDomainSubEnum.v'])
    assert 'stable_hitting_denotational_adequacy' in hitting and 'stable_hitting_admissible' in hitting
    print(f'Soundness source contracts: {len(sources)} modules; no unfinished proofs/new assumptions or capability drift.')


def manifest_check():
    data = json.loads(MANIFEST.read_text())
    names = set(data['soundness'])
    assert len(names) == 199 and names <= {e['name'] for e in data['endpoints']}
    for endpoint in [
        'PTree.Prob.Backend.SubEnum.FreeOmega.JointSoundness.free_omega_qlift_sound',
        'PTree.Prob.Backend.SubEnum.FreeOmega.QuotientSoundness.free_omega_qlift_eq_sound',
        'PTree.Eq.Backend.StableHittingDomainSubEnum.stable_hitting_denotational_adequacy',
        'PTree.Prob.Backend.Common.DomainTransport.oval_bidual_coupled_nat',
    ]:
        assert endpoint in names, 'Missing final contract'


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
        'PTree.Prob.Backend.SubEnumR.FreeOmega.RelationalValidation': [
            'subenumR_native_model_lub', 'subenumR_qlift_bidual_raw',
            'subenumR_qlift_bidual', 'subenumR_qlift_eq_modelable'],
        'PTree.Prob.Backend.SubEnum.FreeOmega.RelationalValidation': [
            'subenum_native_model_lub', 'subenum_qlift_bidual_raw',
            'subenum_generic_qlift_bidual', 'subenum_generic_qlift_tests'],
    }
    policy = json.loads(POLICY.read_text())
    path = 'theories/Regression/Probability/GenericQuotientValidation.v'
    groups['PTree.Regression.Probability.GenericQuotientValidation'] = policy['regressions'][path]
    entries = query([module+'.'+name for module, names in groups.items() for name in names])
    for e in entries:
        assert logical_axioms(e['assumptions']) <= SOUNDNESS_AXIOMS, e['name']
        if e['name'].startswith('PTree.Prob.FreeOmega.Validation.'):
            assert not re.search(r'\b(?:SubEnum\w*|ptree|SemanticOmegaLaws|SemanticMeasureBindLaws)\b', e['type']), e['name']
        if e['name'].endswith('.model_qlift_bidual_raw'):
            assert 'free_omega_modelable' not in e['type'], 'Raw bridge must allow invalid middle terms'
    print(f'{len(entries)} generic quotient/adapter/regression endpoints checked; unchanged logical whitelist.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--source-only', action='store_true')
    parser.add_argument('--generic-quotient-only', action='store_true')
    args = parser.parse_args()
    source_check(); manifest_check(); graph()
    if not args.source_only:
        if not args.generic_quotient_only:
            check('soundness')
        generic_quotient_check()
