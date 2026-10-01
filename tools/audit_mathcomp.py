#!/usr/bin/env python3
"""Isolated Gate M query/parser helpers, called only by audit_contracts.py.

Gate M is NOT a universe-consistency or ordinary kernel-check claim. Its
compiled snapshot records unsafe-hierarchy reports separately from axioms.
"""
from rocq_paths import LOADPATH
import re
import subprocess
from types import SimpleNamespace
from audit_assumptions import ROOT, parse, SOUNDNESS_AXIOMS, logical_axioms
from mathcomp_policy import GATE_M


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
    return entries


def query_gate_m(endpoints, joint=True, axiom_exceptions=None):
    assert len(endpoints) == len(set(endpoints)), 'Duplicate Gate M endpoint'
    commands = ['Require PTree.Tests.AllImports.'] if joint else []
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
    result = subprocess.run(['opam', 'exec', '--', 'coqtop', '-quiet',
                             *LOADPATH], cwd=ROOT,
                            input='\n'.join(commands) + '\n', text=True, capture_output=True)
    return parse_gate_m(result, endpoints, axiom_exceptions)


if __name__ == '__main__':
    raise SystemExit('Helper module: run tools/audit_contracts.py --gate M (optionally --build).')
