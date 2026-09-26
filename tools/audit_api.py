#!/usr/bin/env python3
"""Public module/capability contracts and explicitly scoped kernel checks."""
import argparse
import json
import re
import subprocess
from audit_assumptions import ROOT, MANIFEST, check, without_comments

POLICY = ROOT / 'docs/CONTRACT_POLICY.json'
STRUCTURAL = 'theories/Prob/FreeOmega/StructuralMeasure.v'
STRUCTURAL_INSTANCES = {
    'FreeOmegaSemanticMeasure', 'FreeOmegaSemanticMeasureCoreLaws',
    'FreeOmegaSemanticMeasureAEKleisliLaws', 'FreeOmegaSemanticMeasureCountableAELaws',
    'FreeOmegaSemanticMeasureCouplingAELaws', 'FreeOmegaSemanticMeasureBindLaws',
    'FreeOmegaMixedMeasureLaws', 'FreeOmegaSemanticOmega',
    'FreeOmegaSemanticOmegaLaws', 'FreeOmegaSemanticMeasureOrderLaws',
}
REGISTRY = {'theories/Eq/Backend/' + n + '.v': n + '_CanonicalBehavior'
            for n in ['EnumQ', 'SubEnumQ', 'SubEnumR']}
REGISTRY['theories/Eq/Backend/MathComp/Direct.v'] = 'MathComp_CanonicalBehavior'
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
    'PTree.Regression.Infrastructure.PublicBehavior',
    'PTree.Regression.Infrastructure.CanonicalBehaviorStructuralFirst',
    'PTree.Regression.Infrastructure.CanonicalBehaviorNativeFirst',
    'PTree.Interp.IterationMachine',
    'PTree.Interp.IterationUniform',
    'PTree.Interp.FreeOmega.IterationUniform',
    'PTree.Regression.Semantics.PTreeUniformity',
]


def current_surface(sources):
    """Current routing/ownership contracts; deliberately no proof-text freeze."""
    sources = {p: without_comments(s) for p, s in sources.items()}
    structural = sources[STRUCTURAL]
    for name in STRUCTURAL_INSTANCES:
        assert re.search(r'^#\[local\] Polymorphic Instance ' + name + r'\b', structural, re.M), name
    assert re.search(r'^#\[global\] Polymorphic Instance FreeOmegaMixedMeasure\b', structural, re.M)
    found = {}
    for path, code in sources.items():
        assert not path.startswith('theories/API/'), 'Retired API namespace: ' + path
        for name in STRUCTURAL_INSTANCES:
            for match in re.finditer(r'(?m)^([^\n]*\b(?:Instance|Instances)\s+[^\n]*\b'
                                     + name + r'\b[^\n]*)', code):
                assert '#[local]' in match[0], 'Exported structural registration: ' + path
        for match in re.finditer(r'(?m)^(?:#\[\w+\]\s+)?(?:Polymorphic\s+)?Instance\s+(\w+)'
                                 r'[\s\S]*?\.(?=\s|$)', code):
            if not re.search(r'\bCanonicalBehavior\b', match[0]):
                continue
            assert match[0].startswith('#[global]'), 'Unreviewed route: ' + path
            assert path not in found, 'Duplicate route: ' + path
            found[path] = match[1]
        for name in REGISTRY.values():
            assert not re.search(r'\bExisting\s+Instances?\s+[^.]*\b' + name + r'\b', code), path
    assert found == REGISTRY, ('Canonical registry drift', found)
    behavior = sources['theories/Eq/Canonical.v']
    block = behavior.split('Class CanonicalBehavior', 1)[1].split('}.', 1)[0]
    assert re.findall(r'\b(behavior_\w+)\s*:', block) == [
        'behavior_frontier', 'behavior_measure', 'behavior_mixed', 'behavior_omega']
    assert not re.search(r'Laws|:>|::|admissible|modelable', block), 'Selector is not a law bundle'
    assert not re.search(r'Existing\s+Instances?\s+behavior_', behavior)
    for glyph, owner, module, relation in [
        ('≡ₚ', 'Eq/PStruct', 'PStructNotations', 'pstruct'),
        ('≃ₚ', 'Eq/PStrong', 'PStrongNotations', 'pstrong'),
        ('≈ₚ', 'Eq/Canonical', 'PEuttNotations', 'canonical_peutt')]:
        owner = 'theories/' + owner + '.v'
        # Local notation is a client's explicit interpretation, not a second
        # exported glyph owner. Keep rejecting every nonlocal redefinition.
        matches = {p for p, s in sources.items()
                   for m in re.finditer(r'(?m)^[ \t]*(?:(#\[[^\]]*\])\s*)?'
                                        r'(?:(Local|Global)\s+)?Notation\s+"[^"\n]*' + glyph, s)
                   if m[2] != 'Local' and not (m[1] and re.fullmatch(r'#\[\s*local\s*\]', m[1]))}
        assert matches == {owner}, (glyph, matches)
        block = sources[owner].split('Module ' + module + '.', 1)[1].split('End ' + module + '.', 1)[0]
        assert block.count(':= (' + relation + ' ') == 2, 'Notation interpretation drift'
    bind_owners = {p for p, s in sources.items()
                   if re.search(r'\b(?:Theorem|Lemma|Corollary|Definition|Notation) peutt_bind\b', s)}
    assert bind_owners == {'theories/Eq/Bind.v'}, ('Bind ownership/shadowing', bind_owners)
    client = sources['theories/Regression/Infrastructure/PublicBehavior.v']
    assert re.findall(r'^From .*?\.$', client, re.M) == [
        'From PTree Require Import PTree PTreeFacts.',
        'From PTree.Eq.Backend Require Import SubEnumQ.',
        'From Coq Require Import Morphisms.',
        'From PTree.Eq Require Import PEutt.']
    assert not re.search(r'^\s*Require\b|\b(?:Instance|Hint|Coercion|Arguments)\b', client, re.M)


def facade_surface(text):
    return ' '.join(without_comments(text).split())


def surface_check():
    current_surface({p.relative_to(ROOT).as_posix(): p.read_text()
                     for p in (ROOT / 'theories').rglob('*.v')})
    data = json.loads(POLICY.read_text())
    for path, expected in data['facades'].items():
        assert facade_surface((ROOT / path).read_text()) == expected, 'Public surface changed: ' + path
    manifest = json.loads(MANIFEST.read_text())
    assert len(manifest['api']) == len(set(manifest['api'])) == 266
    assert len(manifest['capability']) == len(set(manifest['capability'])) == 25
    assert set(manifest['capability']) <= set(manifest['api'])
    assert set(manifest['api']) <= {e['name'] for e in manifest['endpoints']}
    print('Public modules and all 266 owner/helper + 25 capability contracts covered.')


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
