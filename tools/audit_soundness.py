#!/usr/bin/env python3
"""Source-only safety contracts; compiled checks belong to audit_contracts.py."""
from rocq_paths import source_files
import argparse
import json
import re
from audit_assumptions import ROOT, without_comments
from mathcomp_policy import universe_source_check, check_build_flags, GATE_M

POLICY = ROOT / 'tools/data/CONTRACT_POLICY.json'


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
        result[match.group(1)] = logic_spelling(
            ' '.join(code[match.start():match.start()+end.end()].split()))
    return result


def logic_spelling(text):
    """Standard Coq Utf8 spellings only; do not erase logical structure."""
    text = text.translate(str.maketrans({
        '∀': 'forall', '∃': 'exists', '→': '->', '↔': '<->',
        '∧': '/\\', '∨': '\\/', '¬': '~', '≠': '<>',
    }))
    # Class fields contain terms, not Ltac functions. Normalize a lambda's
    # own delimiter only: arrows in match branches or nested binders survive.
    parts = re.findall(r"\w[\w']*|=>|\s+|.", text, re.S)
    for i, token in enumerate(parts):
        if token != 'fun':
            continue
        depth = 0
        for j in range(i + 1, len(parts)):
            if parts[j] in ('(', '[', '{'):
                depth += 1
            elif parts[j] in (')', ']', '}'):
                depth -= 1
            elif parts[j] == '=>' and depth == 0:
                parts[i], parts[j] = 'λ', ','
                if parts[j - 1].isspace():
                    parts[j - 1] = ''
                break
            assert depth >= 0, 'Unrecognized lambda binder in class contract'
        else:
            raise AssertionError('Unrecognized lambda in class contract')
    return ' '.join(''.join(parts).split())


def independent_math(sources):
    """Keep the actual external mathematics independent, not only its signatures."""
    forbidden = r'\b(?:FreeOmega|free_omega_\w+|Semantic\w+|ptree|SubEnumQ)\b'
    for path, text in sources.items():
        if path.startswith('theories/Prob/Domain/'):
            assert not re.search(forbidden, code_only(text)), 'Domain is not independent: ' + path
    for name in ['RealTransport', 'CountableRealTransport', 'DomainTransport', 'CountableCoupling']:
        code = code_only(sources['theories/Prob/Backend/Common/' + name + '.v'])
        assert not re.search(forbidden, code), 'Transport mathematics imports program semantics: ' + name
        if name in ['RealTransport', 'CountableRealTransport']:
            assert not re.search(r'\bOmegaVal\b', code), 'Scalar transport depends on the domain'
    hitting = code_only(sources['theories/Prob/FreeOmega/Validation/StableHitting.v'])
    for start, end in [('Section DomainKernel.', 'End DomainKernel.'),
                       ('Definition ptree_model_kernel', 'Definition ptree_model_approx')]:
        assert start in hitting and end in hitting, 'Missing independent kernel block'
        block = hitting.split(start, 1)[1].split(end, 1)[0]
        assert not re.search(r'\b(?:FreeOmega|free_omega_\w+|stable_hitting_approx|ptree_hitting_approx|sem_\w+)\b', block), \
            'Mathematical kernel must not be defined using formal iterates'


def source_check(sources=None, policy=None):
    if sources is None:
        check_build_flags(ROOT)
        sources = {p.relative_to(ROOT).as_posix(): p.read_text() for p in source_files()}
    policy = policy or json.loads(POLICY.read_text())
    found_classes = {}
    for path, text in sources.items():
        code = code_only(text)
        assert not re.search(r'\b(?:PTreeDefinitionNew|ShallowNew)\b|\.bak\b', code), \
            'Obsolete artifact reference: ' + path
        assert not re.search(r'\b(?:Admitted|admit|Axiom|Axioms|Parameter|Parameters)\b', code), \
            'Unfinished proof or semantic assumption: ' + path
        universe_source_check(path, text)
        for name, decl in classes(text).items():
            found_classes[path + ':' + name] = decl
    assert found_classes == {k: logic_spelling(v) for k, v in policy['classes'].items()}, \
        'Capability declaration drift (new or changed Class)'
    independent_math(sources)
    for path, source in sources.items():
        if path.startswith(('theories/Prob/Backend/EnumQ/', 'theories/Prob/Backend/SubEnumQ/',
                            'theories/Prob/Backend/SubEnumR/', 'theories/Examples/')):
            code = code_only(source)
            # A checked negative probe is evidence of absence, not a dependency.
            code = re.sub(r'\bFail\s+Check\s+[^\n]+\.', '', code)
            assert not re.search(r'\b(?:nnQ\w*|Build_nnQ\w*|Qval|rational_shared|rational_unshare)\b', code), path
            assert 'Prob.Legacy' not in code, 'Legacy native dependency: ' + path
    for path, names in policy['clients'].items():
        assert path in sources, 'Missing audited client module: ' + path
        code = code_only(sources[path])
        for name in names:
            assert re.search(r'\b(?:Example|Lemma|Theorem)\s+'+re.escape(name)+r'\b',code), \
                'Missing audited client: ' + name
    # Endpoint types/assumptions and actual Rocq clients protect soundness.
    # Proof tactics, intermediate helper names and recursive proof structure
    # are not a source-level contract.
    print(f'Soundness source contracts: {len(sources)} modules; {len(GATE_M)} explicitly universe-unchecked Gate M modules; no unfinished proofs/new assumptions or capability drift.')


if __name__ == '__main__':
    argparse.ArgumentParser(description=__doc__).parse_args()
    source_check()
