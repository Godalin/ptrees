#!/usr/bin/env python3
"""Separate Gate S build from explicitly universe-unchecked Gate M validation.

Gate M is NOT a universe-consistency or ordinary kernel-check claim. Its
compiled snapshot records unsafe-hierarchy reports separately from axioms.
"""
import argparse
import json
import re
import subprocess
from types import SimpleNamespace
from audit_assumptions import ROOT, parse, SOUNDNESS_AXIOMS, logical_axioms
from audit_architecture import graph
from audit_soundness import source_check
from mathcomp_direct_policy import DIRECT, GATE_M, safe_targets

SNAPSHOT = ROOT / 'docs/MATHCOMP_DIRECT_CONTRACTS.json'
ENDPOINTS = ['PTree.' + DIRECT.replace('/', '.') + '.' + n for n in [
    'mathcomp_direct_mixed', 'mathcomp_direct_tree', 'mathcomp_direct_head',
    'mathcomp_direct_frontier', 'mathcomp_direct_kernel', 'mathcomp_direct_hitting',
    'mathcomp_direct_peutt', 'mathcomp_direct_peutt_refl',
    'mathcomp_direct_hitting_exists', 'mathcomp_direct_approx_unfold',
    'mathcomp_direct_global_le_diagonal', 'mathcomp_direct_split_le_global',
    'mathcomp_direct_bind_cofinal', 'mathcomp_direct_peutt_bind']]
ENDPOINTS += ['PTree.Regression.Backend.MathCompDirect.' + n for n in [
    'direct_ret', 'direct_frontier', 'direct_kernel', 'direct_hitting',
    'direct_ret_reflexivity', 'direct_eventful_reflexivity',
    'available_native_order', 'available_native_omega', 'available_general_hitting_exists',
    'direct_retry_hitting', 'direct_unbounded_retry', 'direct_retry_before_vis',
    'direct_eventful_bind_rewrite', 'direct_nested_unbounded_retry',
    'direct_nested_retry_diagonal', 'direct_retry_vis_interaction']]
# Importing the unchecked modules must not retrospectively taint safe facts.
SAFE_CONTROLS = [
    'PTree.Prob.Backend.MathComp.NativeLaws.mathcomp_native_bind_le_k',
    'PTree.Prob.Backend.MathComp.NativeLaws.MathCompNativeMixedMeasure',
    'PTree.Prob.Backend.MathComp.OmegaLaws.MathCompNativeOmegaLaws',
    'PTree.Prob.Backend.MathComp.OmegaLaws.MathCompNativeFubiniLaws',
    'PTree.Prob.Backend.MathComp.BindLaws.MathCompNativeBindLaws',
    'PTree.Prob.Backend.MathComp.Retry.mathcomp_retry_fixed_point']


def parse_direct(result, endpoints):
    assert result.returncode == 0 and not re.search(r'\bError:', result.stdout + result.stderr), \
        result.stdout + result.stderr
    unsafe = {}
    output = result.stdout
    for i, name in enumerate(endpoints):
        pattern = rf'(AUDIT_AXIOMS_{i}\n)(.*?)(AUDIT_END_{i}\n)'
        matches = list(re.finditer(pattern, output, re.S))
        assert len(matches) == 1, 'Missing/duplicate assumption block: ' + name
        block = matches[0].group(2)
        flags = re.findall(r'^([\w.]+) relies on an unsafe hierarchy\.\s*$', block, re.M)
        theory = 'Theory:\nType hierarchy is collapsed (logic is inconsistent)'
        collapsed = theory in block
        assert not flags or collapsed, 'Unsafe declarations without theory warning: ' + name
        cleaned = re.sub(r'^[\w.]+ relies on an unsafe hierarchy\.\s*\n', '', block, flags=re.M)
        cleaned = cleaned.replace(theory, '')
        if cleaned.strip() == 'Axioms:':
            cleaned = 'Closed under the global context\n'
        output = output[:matches[0].start(2)] + cleaned + output[matches[0].end(2):]
        unsafe[name] = {'unsafe_hierarchy': sorted(flags), 'session_collapsed_universes': collapsed}
    entries = parse(SimpleNamespace(returncode=result.returncode,
                                    stdout=output, stderr=result.stderr), endpoints)
    for entry in entries:
        assert logical_axioms(entry['assumptions']) <= SOUNDNESS_AXIOMS, entry['name']
        entry.update(unsafe[entry['name']])
        if entry['name'] in SAFE_CONTROLS:
            assert not entry['unsafe_hierarchy'], 'Safe native theorem is tainted'
    return entries


def query_direct():
    endpoints = ENDPOINTS + SAFE_CONTROLS
    commands = ['Require PTree.Regression.Infrastructure.AllImports.']
    # Loading Gate M itself merges otherwise inconsistent universe constraints.
    # This dedicated audit session is a direct-backend client, never Gate S.
    commands += ['Local Unset Universe Checking.']
    commands += ['Require PTree.' + m.replace('/', '.') + '.' for m in sorted(GATE_M)]
    commands += ['Set Printing Width 100.', 'Set Printing Depth 1000.', 'Set Printing Implicit.']
    for i, name in enumerate(endpoints):
        for kind, command in [('TYPE', 'Check @' + name),
                              ('AXIOMS', 'Print Assumptions ' + name), ('END', None)]:
            commands.append(f'Goal True. idtac "AUDIT_{kind}_{i}". Abort.')
            if command:
                commands.append(command + '.')
    result = subprocess.run(['opam', 'exec', '--', 'coqtop', '-quiet', '-R',
                             '_build/default/theories', 'PTree'], cwd=ROOT,
                            input='\n'.join(commands) + '\n', text=True, capture_output=True)
    return parse_direct(result, endpoints)


def check():
    expected = json.loads(SNAPSHOT.read_text())
    assert expected['gate_m_modules'] == sorted(GATE_M), 'Reviewed allowlist changed'
    assert expected['endpoints'] == query_direct(), 'Direct compiled type/assumption/unsafe-flag drift'
    print(f'Gate M: {len(ENDPOINTS)} direct endpoints + {len(SAFE_CONTROLS)} safe controls; '
          'types, logical axioms and unsafe-hierarchy reports match. NOT universe-checked.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gate', choices=['S', 'M'], default='M')
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    source_check()
    if args.build:
        targets = safe_targets(ROOT) if args.gate == 'S' else [
            'theories/' + m + '.vo' for m in sorted(GATE_M)]
        subprocess.run(['opam', 'exec', '--', 'dune', 'build', *targets], cwd=ROOT, check=True)
    graph()
    if args.gate == 'M':
        check()
    else:
        print('Gate S: safe-only target selection and dependency separation passed; '
              'run the normal compiled-assumption and targeted kernel audits separately.')
