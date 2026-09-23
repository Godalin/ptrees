#!/usr/bin/env python3
"""Generic structural consumers: exact old-source preservation and proof extraction."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments

BASELINE = '09d0ab2d71ede751093316a0f0f4be2f34705719'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
DIRECT = 'theories/Regression/Backend/MathCompDirect.v'
REL = 'theories/Eq/FreeOmega/Relation.v'
FO_LIMIT = 'theories/Prob/FreeOmega/RelationalLimit.v'
NEW = {'theories/' + p + '.v' for p in [
    'Prob/Interface/RelationalClosure', 'Eq/RelationalHitting', 'Eq/Relation',
    'Prob/Backend/MathComp/RelationalClosure', 'Regression/Semantics/RelationalConsumers']}
IMPORTS = {'Require PTree.' + p.removeprefix('theories/').removesuffix('.v').replace('/', '.') + '.' for p in NEW}
NAMES = {
    'Algebra': ['bind_ret_l', 'bind_ret_r', 'bind_assoc', 'fmap_id', 'fmap_compose', 'fmap_bind'],
    'Iter': ['iter_unfold', 'iter_structural', 'iter_rel', 'iter_natural', 'iter_codiagonal']}
CHANGED = {ALL, DIRECT, REL, FO_LIMIT} | {
    'theories/Eq/' + prefix + owner + '.v' for prefix in ['', 'FreeOmega/'] for owner in NAMES}
DIRECT_NAMES = ['direct_finite_strong', 'direct_structural_bridge_of_relational_lub',
                'direct_codiagonal_of_relational_lub']
ENDPOINTS = ['PTree.' + m + '.' + n for m, names in {
    'Prob.Interface.RelationalClosure': ['relational_bind', 'relational_mixed_bind',
        'relational_zero', 'relational_lub', 'relational_bind_of_laws', 'relational_mixed_bind_of_laws'],
    'Eq.RelationalHitting': ['stable_target_rel', 'stable_target_approx_rel',
        'stable_hitting_approx_rel', 'stable_hitting_rel'],
    'Eq.Relation': ['pstrong_state', 'pstrong_kernel', 'ptree_hitting_pstrong',
        'peutt_of_pstrong', 'peutt_of_pstruct'],
    'Eq.Algebra': ['peutt_' + n for n in NAMES['Algebra']],
    'Eq.Iter': ['peutt_' + n for n in NAMES['Iter']],
    'Prob.FreeOmega.RelationalLimit': ['free_omega_relational_' + n for n in ['bind', 'mixed_bind', 'zero', 'lub']],
    'Prob.Backend.MathComp.RelationalClosure': ['mathcomp_relational_' + n for n in ['bind', 'mixed_bind', 'zero']],
    'Regression.Semantics.RelationalConsumers': ['generic_structural_bridge', 'generic_strong_bridge',
        'generic_structural_iter', 'generic_codiagonal', 'completion_strong', 'completion_assoc',
        'rational_eventful_assoc', 'real_eventful_assoc'],
}.items() for n in names]
WRAPPERS = ['PTree.Eq.FreeOmega.Relation.peutt_of_' + n for n in ['pstruct', 'pstrong']]
WRAPPERS += ['PTree.Eq.FreeOmega.' + m + '.peutt_' + n for m, names in NAMES.items() for n in names]


@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)


def specialize(s, owner, name):
    pattern = r'(Theorem ' + name + r'\b.*?\nProof\.).*?Qed\.'
    tail = '\n  exact Hstep.' if name == 'peutt_iter_rel' else ''
    body = ('\n  apply (' + owner + '.' + name + '\n'
            '    free_omega_relational_bind free_omega_relational_mixed_bind\n'
            '    free_omega_relational_zero free_omega_relational_lub).' + tail + '\nQed.')
    result, count = re.subn(pattern, lambda m: m[1] + body, s, flags=re.S)
    assert count == 1, name
    return result


def check_changes(sources):
    for owner, names in NAMES.items():
        fp = 'theories/Eq/FreeOmega/' + owner + '.v'
        gp = 'theories/Eq/' + owner + '.v'
        expected = 'From PTree.Prob.FreeOmega Require Import RelationalLimit.\n' + frozen(fp)
        for name in names:
            expected = specialize(expected, owner, 'peutt_' + name)
        assert sources[fp] == expected, 'Specialization/signature drift: ' + fp
        s = frozen(fp)
        end = 'End FreeOmegaAlgebra.' if owner == 'Algebra' else 'Section EventlessBehavioralIterationFusion.'
        block = s[s.index('Theorem peutt_'):s.index(end)]
        block = re.sub(r'@peutt E MN MF\s+\(FreeOmegaObservableSemanticMeasure \(NI := NI\) \(NO := NO\)\)\s+'
            r'FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure\s+FreeOmegaObservableSemanticOmega',
            '@peutt E MN MF FI FC MX FO', block)
        block = block.replace('apply peutt_of_pstruct.',
            'apply (Relation.peutt_of_pstruct Hbind Hmixed Hzero Hlimit).')
        prefix = ('From PTree.Prob.Interface Require Import RelationalClosure.\n'
                  'From PTree.Eq Require Import Relation Shallow PStruct.\n') + frozen(gp)
        assert sources[gp].startswith(prefix), 'Old generic theory changed: ' + gp
        tail = sources[gp][len(prefix):]
        assert tail.endswith(block + 'End RelationalAlgebra.\n'), 'Extracted proof changed: ' + gp
        context = without_comments(tail[:-len(block + 'End RelationalAlgebra.\n')])
        expected_context = '''Section RelationalAlgebra.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}.
Variable Hbind : relational_bind FI.
Variable Hmixed : relational_mixed_bind NI FI MX.
Variable Hzero : relational_zero FO.
Variable Hlimit : relational_lub FO.'''
        assert context.split() == expected_context.split(), 'Unreviewed capability context: ' + gp
    expected = 'From PTree.Eq Require Import Relation.\n' + frozen(REL)
    for n in ['peutt_of_pstruct', 'peutt_of_pstrong']:
        expected = specialize(expected, 'Relation', n)
    assert sources[REL] == expected, 'Old structural observations or bridge statements changed'
    prefix = frozen(FO_LIMIT).replace('Require Import Measure Omega.',
        'Require Import Measure Omega Mixed RelationalClosure.').replace(
        '  PTree.Prob.FreeOmega.Measure.',
        '  PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.StructuralMeasure.')
    prefix = prefix.removesuffix('End RelationalLimit.\n')
    assert sources[FO_LIMIT].startswith(prefix) and sources[FO_LIMIT].endswith('End RelationalLimit.\n')
    tail = without_comments(sources[FO_LIMIT][len(prefix):])
    assert re.findall(r'\bTheorem (\w+)', tail) == ['free_omega_relational_' + n for n in ['bind', 'mixed_bind', 'zero', 'lub']]
    for p, code in [(FO_LIMIT, tail)] + [(p, without_comments(sources[p])) for p in NEW]:
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|Class|Instance|Existing|Hint)\b|Unset .*Checking', code), p
    assert sources[DIRECT].startswith(frozen(DIRECT)), 'Existing Gate M proof changed'
    tail = without_comments(sources[DIRECT][len(frozen(DIRECT)):])
    assert re.findall(r'\bExample (\w+)', tail) == DIRECT_NAMES
    assert not re.search(r'\b(?:Axiom|Parameter|Admitted|Class|Instance|Hint|Inductive|CoFixpoint)\b|Unset .*Checking', tail)
    assert 'Variable Hlimit : relational_lub NO.' in tail, 'MathComp limit must remain explicit'
    assert tail.index('Variable Hlimit') > tail.index('Example direct_finite_strong')
    for p in ['theories/Eq/Relation.v', 'theories/Eq/RelationalHitting.v',
              'theories/Prob/Interface/RelationalClosure.v']:
        assert not re.search(r'FreeOmega|FOQL|MathComp|SubEnum|OmegaVal', without_comments(sources[p])), p
    closure = without_comments(sources['theories/Prob/Interface/RelationalClosure.v'])
    assert 'sem_increasing c -> sem_increasing d ->' in closure
    assert not re.search(r'peutt|pstruct|pstrong|ptree', closure)
    bridge = without_comments(sources['theories/Eq/Relation.v'])
    assert 'peutt_coinduction' in bridge and 'stable_hitting_approx_rel' in bridge
    assert not re.search(r'\b(?:Hypothesis|Variable)\s+\w+\s*:.*(?:peutt|pstruct|pstrong)', bridge)


def previous_sources(sources):
    """Validate this migration before presenting the precise frozen old view.

    Older mutation tests still run against their own source; unapproved old
    changes are never hidden. Not a generic reset-to-baseline escape hatch.
    """
    from audit_effect_execution import previous_sources as execution_sources
    sources = execution_sources(sources)
    if 'theories/Eq/Relation.v' not in sources:
        return sources
    check_changes(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    for p in CHANGED - {ALL}:
        result[p] = frozen(p)
    for line in IMPORTS:
        assert result[ALL].splitlines().count(line) == 1, 'Missing/duplicate new import: ' + line
        result[ALL] = result[ALL].replace(line + '\n', '')
    return result


def check_source(sources):
    from audit_effect_execution import previous_sources as execution_sources
    sources = execution_sources(sources)
    old = {p for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
           cwd=ROOT, text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW, 'Unapproved addition/deletion'
    previous = previous_sources(sources)
    for p in old:
        assert previous[p] == frozen(p), 'Frozen source changed: ' + p
    for p in ['docs/CONTRACTS.json', 'docs/MATHCOMP_DIRECT_CONTRACTS.json']:
        assert (ROOT / p).read_text() == frozen(p), 'Do not refresh old contracts: ' + p
    print('Exact eleven-proof extraction, thirteen specializations, old source/signature conservation passed.')


def compiled_check():
    snapshot = json.loads((ROOT / 'docs/RELATIONAL_CONSUMER_CONTRACTS.json').read_text())
    assert snapshot['baseline'] == BASELINE
    frozen_endpoints = {e['name']: e for e in json.loads(frozen('docs/CONTRACTS.json'))['endpoints']}
    assert snapshot['before_wrappers'] == [frozen_endpoints[n] for n in WRAPPERS]
    results = query(ENDPOINTS + WRAPPERS)
    compare(snapshot['endpoints'], results)
    for e in results:
        assert logical_axioms(e['assumptions']) <= SOUNDNESS_AXIOMS, e['name']
        if e['name'].startswith(('PTree.Eq.Relation.', 'PTree.Eq.RelationalHitting.',
                                  'PTree.Eq.Algebra.', 'PTree.Eq.Iter.')):
            assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal', e['type']), e['name']
    old = {e['name']: e for e in snapshot['before_wrappers']}
    for e in results:
        if e['name'] in old:
            assert e['type'] == old[e['name']]['type'], e['name']
            assert logical_axioms(e['assumptions']) <= logical_axioms(old[e['name']]['assumptions']), e['name']
    print(f'{len(results)} compiled generic/backend/wrapper contracts checked; old wrapper types unchanged.')


def query_direct():
    import audit_mathcomp_direct as direct
    saved = direct.ENDPOINTS
    try:
        direct.ENDPOINTS = ['PTree.Regression.Backend.MathCompDirect.' + n for n in DIRECT_NAMES]
        entries = direct.query_direct()
        for e in entries:
            if e['name'].endswith('direct_finite_strong'):
                assert 'relational_lub' not in e['type'], e['name']
            elif e['name'].endswith('_of_relational_lub'):
                assert 'relational_lub' in e['type'], e['name']
        return entries
    finally:
        direct.ENDPOINTS = saved


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    parser.add_argument('--direct', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT / 'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
    if args.direct:
        assert query_direct() == json.loads((ROOT / 'docs/RELATIONAL_CONSUMER_DIRECT_CONTRACTS.json').read_text())['endpoints']
        print('Three conditional/finite Gate M clients + safe controls checked; NOT universe-checked.')
