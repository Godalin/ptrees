#!/usr/bin/env python3
"""Curated API/capability contracts and explicitly scoped kernel checks."""
import argparse
import json
import subprocess
from audit_assumptions import ROOT, MANIFEST, check, without_comments

POLICY = ROOT / 'docs/CONTRACT_POLICY.json'
KERNEL_MODULES = [
    'PTree.Regression.Infrastructure.AllImports',
    'PTree.Regression.Infrastructure.ArchitectureBoundaries',
    'PTree.Regression.Infrastructure.UniverseSeparatedPTree',
    'PTree.Regression.Backend.UnifiedFrontierEnumQ',
    'PTree.Regression.Semantics.CanonicalPartialDivergence',
    'PTree.Regression.Semantics.PEuttAlgebra',
    'PTree.Regression.Semantics.PublicSemanticFacade',
    'PTree.Regression.Backend.FreeOmegaUpperContracts',
    'PTree.Regression.Probability.FreeOmegaDomain',
    'PTree.Regression.Probability.FreeOmegaSoundness',
    'PTree.Regression.Probability.CountableCoupling',
    'PTree.Regression.Probability.StableHittingDomain',
    'PTree.Regression.Probability.IrrationalHitting',
    'PTree.Regression.Probability.OmegaVal',
    'PTree.Regression.Probability.OmegaValMeasure',
    'PTree.Regression.Probability.RealTransport',
]


def facade_surface(text):
    return ' '.join(without_comments(text).split())


def surface_check():
    data = json.loads(POLICY.read_text())
    for path, expected in data['facades'].items():
        assert facade_surface((ROOT / path).read_text()) == expected, 'Public surface changed: ' + path
    manifest = json.loads(MANIFEST.read_text())
    assert len(manifest['api']) == len(set(manifest['api'])) == 306
    assert len(manifest['capability']) == len(set(manifest['capability'])) == 25
    assert set(manifest['capability']) <= set(manifest['api'])
    assert set(manifest['api']) <= {e['name'] for e in manifest['endpoints']}
    print('Curated facades and all 306 API/helper + 25 capability contracts covered.')


def kernel_check():
    # Check these module bodies together, in the full-library universe context.
    # -norec trusts compiled dependencies; do not call this recursive or exhaustive.
    selected = [arg for module in KERNEL_MODULES for arg in ('-norec', module)]
    subprocess.run(['opam', 'exec', '--', 'coqchk', '-silent', '-R',
                    '_build/default/theories', 'PTree', *selected], cwd=ROOT, check=True)
    print(f'Targeted joint kernel check passed ({len(KERNEL_MODULES)} module bodies; dependencies not rechecked).')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--surface-only', action='store_true')
    parser.add_argument('--kernel', action='store_true')
    args = parser.parse_args()
    surface_check()
    if not args.surface_only:
        check('api')
    if args.kernel:
        kernel_check()
