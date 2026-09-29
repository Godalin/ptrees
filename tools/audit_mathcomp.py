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
from mathcomp_policy import ASSEMBLY, GATE_M, safe_targets

SNAPSHOT = ROOT / 'docs/MATHCOMP_CONTRACTS.json'
ENDPOINTS = ['PTree.' + ASSEMBLY.replace('/', '.') + '.' + n for n in [
    'mathcomp_mixed', 'mathcomp_tree', 'mathcomp_head',
    'mathcomp_frontier', 'mathcomp_kernel', 'mathcomp_hitting',
    'mathcomp_peutt', 'mathcomp_peutt_refl',
    'mathcomp_hitting_exists',
    'mathcomp_bind_cofinal', 'mathcomp_peutt_bind']]
ENDPOINTS += ['PTree.Regression.Backend.MathComp.' + n for n in [
    'ret', 'frontier', 'kernel', 'hitting',
    'ret_reflexivity', 'eventful_reflexivity',
    'available_native_order', 'available_native_omega', 'available_general_hitting_exists',
    'retry_hitting', 'unbounded_retry', 'retry_before_vis',
    'eventful_bind_rewrite', 'nested_unbounded_retry',
    'nested_retry_diagonal', 'retry_vis_interaction',
    'heterogeneous_bind', 'bind_setoid',
    'continuation_setoid', 'fmap_setoid',
    'eventful_iter', 'handler_guarded',
    'guarded_interp', 'guarded_tau']]
ENDPOINTS += [
    'PTree.Eq.Backend.MathComp.MathComp_CanonicalBehavior',
    'PTree.Regression.Backend.MathComp.canonical_profile']
# Importing the unchecked modules must not retrospectively taint safe facts.
SAFE_CONTROLS = [
    'PTree.Prob.Backend.MathComp.NativeLaws.mathcomp_native_bind_le_k',
    'PTree.Prob.Backend.MathComp.NativeLaws.MathCompNativeMixedMeasure',
    'PTree.Prob.Backend.MathComp.OmegaLaws.MathCompNativeOmegaLaws',
    'PTree.Prob.Backend.MathComp.OmegaLaws.MathCompNativeFubiniLaws',
    'PTree.Prob.Backend.MathComp.BindLaws.MathCompNativeBindLaws',
    'PTree.Prob.Backend.MathComp.Retry.mathcomp_retry_fixed_point']


def parse_gate_m(result, endpoints, axiom_exceptions=None):
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
        allowed = SOUNDNESS_AXIOMS | set((axiom_exceptions or {}).get(entry['name'], []))
        assert logical_axioms(entry['assumptions']) <= allowed, entry['name']
        entry.update(unsafe[entry['name']])
        if entry['name'] in SAFE_CONTROLS:
            assert not entry['unsafe_hierarchy'], 'Safe native theorem is tainted'
    return entries


def query_gate_m(endpoints=None, joint=True, axiom_exceptions=None):
    endpoints = ENDPOINTS + SAFE_CONTROLS if endpoints is None else endpoints
    assert len(endpoints) == len(set(endpoints)), 'Duplicate Gate M endpoint'
    commands = ['Require PTree.Regression.Infrastructure.AllImports.'] if joint else []
    # Loading Gate M itself merges otherwise inconsistent universe constraints.
    # This dedicated audit session is a MathComp backend client, never Gate S.
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
    return parse_gate_m(result, endpoints, axiom_exceptions)


def check():
    expected = json.loads(SNAPSHOT.read_text())
    assert expected['gate_m_modules'] == sorted(GATE_M), 'Reviewed allowlist changed'
    assert expected['endpoints'] == query_gate_m(), 'MathComp compiled type/assumption/unsafe-flag drift'
    print(f'Gate M: {len(ENDPOINTS)} backend endpoints + {len(SAFE_CONTROLS)} safe controls; '
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
