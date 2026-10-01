#!/usr/bin/env python3
"""Source-level public boundaries and explicitly scoped kernel checks."""
from rocq_paths import source_files, LOADPATH
import argparse
import json
import re
import subprocess
from audit_assumptions import ROOT, without_comments

POLICY = ROOT / 'tools/data/CONTRACT_POLICY.json'
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
REGISTRY['theories/Eq/Backend/MathComp.v'] = 'MathComp_CanonicalBehavior'
KERNEL_MODULES = [
    # Check the template-polymorphic native sampler client in the full safe
    # context, not just alone (which misses an over-specialized carrier).
    'PTree.Examples.Execution.Runner',
    'PTree.Tests.AllImports',
    'PTree.Tests.Imports.ArchitectureBoundaries',
    'PTree.Tests.Imports.UniverseSeparatedPTree',
    'PTree.Tests.Universe.UnifiedFrontierEnumQ',
    'PTree.Examples.Effects.CanonicalPartialDivergence',
    'PTree.Tests.Rewriting.PEuttAlgebra',
    'PTree.Tests.Imports.PublicSemanticFacade',
    'PTree.Examples.Validation.FreeOmegaUpperContracts',
    'PTree.Examples.Validation.FreeOmegaDomain',
    'PTree.Examples.Validation.FreeOmegaSoundness',
    'PTree.Examples.Validation.CountableCoupling',
    'PTree.Examples.Validation.StableHittingDomain',
    'PTree.Examples.Validation.IrrationalHitting',
    'PTree.Examples.Validation.OmegaVal',
    'PTree.Examples.Validation.OmegaValMeasure',
    'PTree.Examples.Validation.RealTransport',
    'PTree.Tests.Imports.PublicBehavior',
    'PTree.Tests.ImportOrder.CanonicalBehaviorStructuralFirst',
    'PTree.Tests.ImportOrder.CanonicalBehaviorNativeFirst',
    'PTree.Interp.IterationMachine',
    'PTree.Interp.IterationUniform',
    'PTree.Interp.FreeOmega.IterationUniform',
    'PTree.Tests.Capabilities.PTreeUniformity',
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
    client = sources['tests/Imports/PublicBehavior.v']
    imports = facade_surface(client, imports_only=True)
    assert not imports['exports'], 'Public client must not re-export modules'
    assert imports['imports'] == sorted([
        'PTree.PTree', 'PTree.PTreeFacts', 'PTree.Eq.Backend.SubEnumQ',
        'Coq.Morphisms', 'PTree.Eq.PEutt'])
    assert not re.search(r'\b(?:Instance|Hint|Coercion|Arguments)\b', client)


def facade_surface(text, imports_only=False):
    """Small facade grammar: imports/exports and short aliases, not whole proofs.

    Import grouping and whitespace do not matter. Export order remains relevant
    to name precedence; no unreviewed command may hide in a pure facade.
    """
    surface = {'imports': [], 'exports': [], 'aliases': {}}
    commands = re.split(r'\.(?=\s|$)', without_comments(text))
    for command in commands:
        command = ' '.join(command.split())
        if not command:
            continue
        match = re.fullmatch(r'(?:From ([\w.]+) )?Require (Import|Export) ([\w. ]+)', command)
        if match:
            prefix, kind, modules = match.groups()
            names = [(prefix + '.' if prefix else '') + m for m in modules.split()]
            surface['imports' if kind == 'Import' else 'exports'].extend(names)
        elif not imports_only:
            match = re.fullmatch(r'Export ([\w. ]+)', command)
            alias = re.fullmatch(r'Notation (\w+) := ([\w.]+)', command)
            if match:
                surface['exports'].extend(match[1].split())
            elif alias:
                assert alias[1] not in surface['aliases'], 'Duplicate public alias'
                surface['aliases'][alias[1]] = alias[2]
            else:
                raise AssertionError('Unexpected facade command: ' + command)
        else:
            assert not re.match(r'(?:From|Require|Export|Import)\b', command), command
    surface['imports'].sort()
    return surface


def surface_check():
    current_surface({p.relative_to(ROOT).as_posix(): p.read_text()
                     for p in source_files()})
    data = json.loads(POLICY.read_text())
    for path, expected in data['facades'].items():
        assert facade_surface((ROOT / path).read_text()) == expected, 'Public surface changed: ' + path
    print('Public imports/exports, aliases, routing and notation ownership checked.')


def kernel_check():
    # Check these module bodies together, in the full-library universe context.
    # -norec trusts compiled dependencies; do not call this recursive or exhaustive.
    selected = [arg for module in KERNEL_MODULES for arg in ('-norec', module)]
    subprocess.run(['opam', 'exec', '--', 'coqchk', '-silent',
                    *LOADPATH, *selected], cwd=ROOT, check=True)
    print(f'Targeted joint kernel check passed ({len(KERNEL_MODULES)} module bodies; dependencies not rechecked).')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel', action='store_true', help='Also run targeted joint coqchk')
    args = parser.parse_args()
    surface_check()
    if args.kernel:
        kernel_check()
