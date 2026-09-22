#!/usr/bin/env python3
"""Final carrier migration boundary, independent of historical rename-only gates.

Representation-specific proofs may change. Generic theories, MathComp and the
real backend (except its Q-to-R adapter) must remain byte-for-byte conserved.
The compiled comparison only normalizes explicitly reviewed owner relocations
and the definitional rat carrier projection, never premises or logical axioms.
"""
import argparse
import difflib
import json
import re
import subprocess
from pathlib import Path
from audit_assumptions import ROOT, MANIFEST, query, logical_axioms, without_comments

BASELINE = '1cba6c5'
EXCEPTIONS = {
    'theories/Eq/Backend/EnumQCofinality.v',
    'theories/Semantics/Backend/MDPEmbeddingSubEnumQ.v',
    'theories/Prob/Backend/SubEnumR/RationalEmbedding.v',
}
PROTECTED = ('theories/Core/', 'theories/API/', 'theories/Eq/',
             'theories/Semantics/', 'theories/Interp/', 'theories/Prob/Interface/',
             'theories/Prob/FreeOmega/', 'theories/Prob/Domain/',
             'theories/Prob/Backend/MathComp/', 'theories/Prob/Backend/SubEnumR/')


def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT)


def normalize_type(text):
    text = re.sub(r'\bMeasure\.(SubEnumQ|subenumQ_raw|subenumQ_ret|subenumQ_zero|'
                  r'subenumQ_bind|subenumQ_bound|enumQ_mass|enumQ_subprob)\b',
                  r'Representation.\1', text)
    text = text.replace('Iteration.enumQ_expect', 'Representation.EnumQ.enumQ_expect')
    text = ' '.join(text.split())
    return text.replace('ssrnum.Num.NumDomain.sort rat.rat_rat__canonical__Num_NumDomain',
                        'rat.rat')


def native_boundary(source):
    code = without_comments(source)
    assert not re.search(r'\b(?:nnQ\w*|Build_nnQ\w*|Qval|rational_shared|rational_unshare)\b', code), \
        'Legacy scalar or runtime conversion in maintained finite code'
    assert 'Prob.Legacy' not in code, 'Native finite backend imports legacy syntax'


def source_check():
    paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
                                    cwd=ROOT, text=True).splitlines()
    conserved = []
    for path in paths:
        if path.endswith('.v') and path.startswith(PROTECTED) and path not in EXCEPTIONS:
            assert (ROOT / path).read_bytes() == frozen(path), 'Protected theory changed: ' + path
            conserved.append(path)
    for folder in ['theories/Prob/Backend/EnumQ', 'theories/Prob/Backend/SubEnumQ',
                   'theories/Prob/Backend/SubEnumR', 'theories/Examples']:
        for path in (ROOT / folder).rglob('*.v'):
            native_boundary(path.read_text())
    rational = (ROOT/'theories/Prob/Backend/EnumQ/Representation.v').read_text()
    bounded = (ROOT/'theories/Prob/Backend/SubEnumQ/Representation.v').read_text()
    assert 'Definition EnumQ (A : Type) := FiniteEnum rat_rat__canonical__Num_NumDomain A.' in rational
    assert 'Definition SubEnumQ (A : Type) := FiniteSubdist rat_rat__canonical__Num_NumDomain A.' in bounded
    bridge = (ROOT/'theories/Prob/Backend/SubEnumR/RationalEmbedding.v').read_text()
    assert 'finite_subdist_map_weights rational_scalar_monotone mu' in bridge
    assert not (ROOT/'theories/Prob/Backend/Common/RatSubTypes.v').exists()
    assert (ROOT/'theories/Prob/Legacy/RatSubTypes.v').exists()
    print(f'{len(conserved)} protected theory modules byte-for-byte unchanged; '
          'shared carriers, scalar transport and legacy exclusion checked.')


def compare_contracts(old, new):
    assert len(old) == len(new), 'Endpoint loss'
    for before, after in zip(old, new):
        assert before['name'] == after['name'], 'Endpoint renamed or reordered'
        assert normalize_type(before['type']) == normalize_type(after['type']), \
            'Unreviewed compiled type change: ' + before['name']
        old_axioms = logical_axioms(before['assumptions'])
        new_axioms = logical_axioms(after['assumptions'])
        assert new_axioms <= old_axioms, \
            'Added logical assumption: ' + before['name']
        if new_axioms == old_axioms:
            assert normalize_type(before['assumptions']) == normalize_type(after['assumptions']), \
                'Logical assumption statement changed: ' + before['name']
        elif new_axioms:
            # This migration only removes a sole extensionality dependency.
            # A different partial reduction needs an explicit separate review.
            raise AssertionError('Unreviewed partial assumption reduction: ' + before['name'])


def finite_helpers_check():
    modules = ['FiniteEnum', 'FiniteSubdist', 'FiniteAtoms', 'FiniteListAlgebra',
               'FiniteScalarMap', 'FinitePositions', 'FinitePruning',
               'FinitePresentation', 'FiniteSupport', 'FiniteIndexedBind',
               'FiniteRecordExtensionality']
    endpoints = []
    for module in modules:
        source = without_comments((ROOT/f'theories/Prob/Backend/Common/{module}.v').read_text())
        endpoints += ['PTree.Prob.Backend.Common.' + module + '.' + name
                      for name in re.findall(r'\b(?:Lemma|Theorem)\s+(\w+)', source)]
    source = (ROOT/'theories/Regression/Backend/FiniteBackendConsolidation.v').read_text()
    endpoints += ['PTree.Regression.Backend.FiniteBackendConsolidation.' + name
                  for name in re.findall(r'\b(?:Example|Lemma|Theorem)\s+(\w+)', source)]
    for entry in query(endpoints):
        allowed = {'FunctionalExtensionality.functional_extensionality_dep'} \
            if '.FiniteRecordExtensionality.' in entry['name'] else set()
        if entry['name'].rsplit('.', 1)[-1] in {
                'real_subdistribution_is_shared', 'rational_to_real_uses_shared_transport',
                'high_carrier_bridge'}:
            # The concrete realType adapter inherits MathComp's established
            # classical structure; no such allowance applies to generic algebra.
            allowed = {'boolp.propositional_extensionality',
                       'boolp.functional_extensionality_dep',
                       'boolp.constructive_indefinite_description'}
        assert logical_axioms(entry['assumptions']) <= allowed, entry
    print(f'{len(endpoints)} finite-helper/new-regression endpoints checked: '
          'closed algebra, optional functional extensionality, '
          'explicit inherited MathComp axioms for realType regression endpoints.')


def compiled_check(emit_patch=False):
    baseline = json.loads(frozen('docs/CONTRACTS.json'))
    actual = query([e['name'] for e in baseline['endpoints']], baseline['modules'])
    compare_contracts(baseline['endpoints'], actual)
    if emit_patch:
        # Emission only: the caller reviews/applies the patch. Never recapture
        # an arbitrary new baseline or bypass comparison with the frozen one.
        current_text = MANIFEST.read_text()
        current = json.loads(current_text)
        assert {k:v for k,v in current.items() if k != 'endpoints'} == \
               {k:v for k,v in baseline.items() if k != 'endpoints'}
        current['endpoints'] = actual
        updated = json.dumps(current, indent=2, ensure_ascii=False) + '\n'
        diff = ''.join(list(difflib.unified_diff(current_text.splitlines(True),
                                                updated.splitlines(True)))[2:])
        diff = re.sub(r'@@[^\n]*@@', '@@', diff)
        if diff:
            print('*** Begin Patch\n*** Update File: docs/CONTRACTS.json\n' + diff + '*** End Patch')
    else:
        print(f"{len(actual)} frozen endpoint types preserved after explicit relocation; no added axioms.")
        finite_helpers_check()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-only', action='store_true')
    parser.add_argument('--emit-reviewed-snapshot-patch', action='store_true')
    args = parser.parse_args()
    if not args.emit_reviewed_snapshot_patch:
        source_check()
    if not args.source_only:
        compiled_check(args.emit_reviewed_snapshot_patch)
