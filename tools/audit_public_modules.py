#!/usr/bin/env python3
"""ITree-style module migration: source conservation and frozen contract map."""
import argparse
import json
import re
import subprocess
from audit_assumptions import ROOT, without_comments, query, logical_axioms, SOUNDNESS_AXIOMS
from public_module_migration import (BASELINE, MOVES, REMOVED, frozen, aliases,
    endpoint, text_relocation, expected_contracts, expected_mathcomp, registry_check)
from audit_behavior_routing import structural_check, STRUCTURAL


def tokens(text):
    return ' '.join(without_comments(text).split())


def source_relocation(source):
    source = source.replace('From PTree.API Require Import Behavior BehaviorFreeOmega.',
        'From PTree.Eq Require Import Canonical.\nFrom PTree.Eq.FreeOmega Require Import Canonical.')
    source = source.replace('From PTree.API Require Import Behavior.', 'From PTree.Eq Require Import Canonical.')
    return text_relocation(source)


def production_check(path, old, new):
    expected = source_relocation(old)
    if path == 'theories/Eq/PEutt.v':
        expected = re.sub(r'\bpeutt_bind\b', 'peutt_bind_cofinal', expected)
    if path == 'theories/Eq/FreeOmega/Bind.v':
        expected = expected.replace('eapply peutt_bind.', 'eapply peutt_bind_cofinal.')
    if path in ['theories/Eq/PStruct.v', 'theories/Eq/PStrong.v', 'theories/API/Behavior.v']:
        new = re.sub(r'Module (?:PStruct|PStrong|PEutt)Notations\.[\s\S]*?End \w+Notations\.', '', new)
    if path in ['theories/API/EnumQ.v', 'theories/API/SubEnumQ.v']:
        # Disposition explicitly removes the old convenience programs. The
        # selector constant, including its universe modifier, stays identical.
        pattern = r'#\[global\] Polymorphic Instance [\s\S]*?\.(?=\s|$)'
        assert tokens(re.search(pattern, old)[0]) == tokens(re.search(pattern, new)[0]), path
        native = 'SubEnumQ' if path.endswith('/SubEnumQ.v') else 'EnumQ'
        prefix = f'From PTree.Prob.Backend.{native} Require Import Measure.\n'
        prefix += (f'From PTree.Prob.Backend.{native} Require Export Representation.\n'
                   if native == 'SubEnumQ' else 'Require Export PTree.Prob.Backend.EnumQ.Representation.\n')
        prefix += 'From PTree.Eq Require Import Canonical.\nFrom PTree.Eq.FreeOmega Require Import Canonical.\n'
        if native == 'EnumQ': prefix += 'Export EnumQ.\n'
        assert tokens(re.sub(pattern, '', new)) == tokens(prefix), 'Unreviewed backend assembly: ' + path
        return
    if path == 'theories/API/SubEnumR.v':
        expected = expected.replace('From PTree.API Require Import Behavior BehaviorFreeOmega.',
            'From PTree.Eq Require Import Canonical.\nFrom PTree.Eq.FreeOmega Require Import Canonical.')
        expected = expected.replace('From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.',
            'From PTree.Prob.Backend.SubEnumR Require Export Representation.\nFrom PTree.Prob.Backend.SubEnumR Require Import Measure Coupling Omega.')
    assert tokens(expected) == tokens(new), 'Unexpected production edit: ' + path


def surface_check(sources):
    assert not any(p.startswith('theories/API/') for p in sources), 'API namespace resurrected'
    glyphs = {'≡ₚ': ('theories/Eq/PStruct.v', 'PStructNotations', 'pstruct'),
              '≃ₚ': ('theories/Eq/PStrong.v', 'PStrongNotations', 'pstrong'),
              '≈ₚ': ('theories/Eq/Canonical.v', 'PEuttNotations', 'canonical_peutt')}
    for glyph, (owner, module, relation) in glyphs.items():
        found = [p for p, s in sources.items() if re.search(r'Notation "[^"\n]*' + glyph, without_comments(s))]
        assert found == [owner], (glyph, found)
        block = without_comments(sources[owner]).split('Module ' + module + '.', 1)[1].split('End ' + module + '.', 1)[0]
        assert block.count(':= (' + relation + ' ') == 2, 'Notation changed interpretation'
    declarations = []
    for path, source in sources.items():
        code = without_comments(source)
        if re.search(r'\b(?:Theorem|Lemma|Corollary|Definition|Notation) peutt_bind\b', code):
            declarations.append(path)
    assert declarations == ['theories/Eq/FreeOmega/Bind.v'], ('Bind ownership/shadowing', declarations)
    for path in ['theories/PTree.v', 'theories/Eq.v', 'theories/PTreeFacts.v']:
        code = without_comments(sources[path])
        assert not re.search(r'\b(?:Notation|Definition|Instance|Class|Theorem|Lemma)\b', code), path
    client = without_comments(sources['theories/Regression/Infrastructure/PublicBehavior.v'])
    imports = re.findall(r'^From .*?\.$', client, re.M)
    assert imports == ['From PTree Require Import PTree PTreeFacts.',
                       'From PTree.Eq.Backend Require Import SubEnumQ.',
                       'From PTree.Eq Require Import PEutt.'], imports
    assert not re.search(r'^\s*Require\b|\b(?:Instance|Hint|Coercion|Arguments)\b', client, re.M)
    assert 'eapply peutt_bind; eassumption.' in client


def source_check():
    sources = {p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')}
    old_paths = {p for p in subprocess.check_output(['git','ls-tree','-r','--name-only',BASELINE],
        cwd=ROOT,text=True).splitlines() if p.endswith('.v')}
    move_paths = {'theories/' + a + '.v': 'theories/' + b + '.v' for a,b in MOVES.items()}
    retired = {'theories/API/' + n + '.v' for n in ['Generic','FreeOmega','Weighted']}
    assert set(sources) == (old_paths - retired - set(move_paths)) | set(move_paths.values()) | {
        'theories/Eq.v', 'theories/PTreeFacts.v'}, 'Unreviewed module addition/deletion'
    count = 0
    for path in sorted(old_paths):
        if path in retired or path == 'theories/PTree.v' or '/Regression/' in path:
            continue
        new_path = move_paths.get(path, path)
        production_check(path, frozen(path), sources[new_path])
        count += 1
    from audit_behavior_routing import frozen as foundation
    internal = structural_check(foundation(STRUCTURAL), sources[STRUCTURAL])
    registry_check(sources, internal)
    surface_check(sources)
    assert json.loads((ROOT/'docs/CONTRACTS.json').read_text()) == expected_contracts(), 'Frozen contract migration drift'
    assert json.loads((ROOT/'docs/MATHCOMP_DIRECT_CONTRACTS.json').read_text()) == expected_mathcomp(), 'Gate M migration drift'
    from audit_architecture import aggregate_check
    aggregate_check()
    print(f'{count} retained production modules conserved modulo declared relocation/notation/bind rename.')
    print('505 old contracts accounted for: 10 retired conveniences + 30 alias duplicates + 465 unique owners.')


def compiled_check():
    from audit_assumptions import check
    check()
    manifest = json.loads(frozen('docs/CONTRACTS.json'))
    bind = next(e for e in manifest['endpoints'] if e['name']=='PTree.Eq.FreeOmega.Bind.peutt_bind')
    entries = query(['PTree.Regression.Infrastructure.PublicBehavior.public_bind_owner',
                     'PTree.Eq.FreeOmega.Bind.peutt_bind'])
    assert entries[0]['type'].split(':',1)[1] == entries[1]['type'].split(':',1)[1]
    assert entries[0]['assumptions'] == bind['assumptions']
    endpoints = []
    for module in ['CanonicalBehavior','CanonicalBehaviorNativeFirst','CanonicalBehaviorStructuralFirst','PublicBehavior']:
        path = ROOT/'theories/Regression/Infrastructure'/f'{module}.v'
        endpoints += ['PTree.Regression.Infrastructure.' + module + '.' + n
                      for n in re.findall(r'^(?:Example|Definition) (\w+)', without_comments(path.read_text()), re.M)]
    allowed = SOUNDNESS_AXIOMS | logical_axioms(bind['assumptions'])
    for entry in query(endpoints):
        assert logical_axioms(entry['assumptions']) <= allowed, entry['name']
    print(f'{len(endpoints)} public/import-order endpoints checked; no new logical-axiom allowance.')


def kernel_check():
    modules = ['PTree','Eq','PTreeFacts','Eq.Canonical','Eq.FreeOmega.Canonical',
        'Eq.Backend.EnumQ','Eq.Backend.SubEnumQ','Eq.Backend.SubEnumR',
        'Eq.PStruct','Eq.PStrong','Eq.PEutt','Eq.FreeOmega.Bind',
        'Regression.Infrastructure.PublicBehavior','Regression.Infrastructure.ArchitectureBoundaries',
        'Regression.Infrastructure.CanonicalBehavior','Regression.Infrastructure.CanonicalBehaviorNativeFirst',
        'Regression.Infrastructure.CanonicalBehaviorStructuralFirst','Regression.Infrastructure.StructuralRegistry',
        'Regression.Infrastructure.AllImports','Regression.Semantics.PublicSemanticFacade']
    cmd = ['opam','exec','--','coqchk','-silent','-R','_build/default/theories','PTree']
    for module in modules:
        cmd += ['-norec','PTree.'+module]
    subprocess.run(cmd,cwd=ROOT,check=True)
    print(f'{len(modules)} safe module bodies kernel-checked jointly (-norec; dependencies trusted; Gate M excluded).')


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--compiled',action='store_true'); p.add_argument('--kernel',action='store_true')
    args=p.parse_args(); source_check()
    if args.compiled: compiled_check()
    if args.kernel: kernel_check()
