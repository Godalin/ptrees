#!/usr/bin/env python3
"""Stable compiled contracts and logical assumptions. Read-only; no baseline regeneration."""
import argparse
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs/CONTRACTS.json"
SOUNDNESS_AXIOMS = {
    "boolp.propositional_extensionality", "boolp.functional_extensionality_dep",
    "FunctionalExtensionality.functional_extensionality_dep",
    "boolp.constructive_indefinite_description", "Eqdep.Eq_rect_eq.eq_rect_eq",
    "Description.constructive_definite_description", "Classical_Prop.classic",
}


def without_comments(text):
    """Remove nested Coq comments, preserving quoted strings and newlines."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if not depth and text[i] == '"':
            out.append(text[i]); i += 1
            if quoted and i < len(text) and text[i] == '"':
                out.append(text[i]); i += 1
            else:
                quoted = not quoted
        elif not quoted and text[i:i+2] == '(*':
            depth += 1; out.append(' '); i += 2
        elif depth and text[i:i+2] == '*)':
            depth -= 1; out.append(' '); i += 2
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' '); i += 1
    assert depth == 0 and not quoted, "Unclosed Coq comment/string"
    return ''.join(out)


def clean(block):
    block = re.sub(r"\n\d+ goals?\b[\s\S]*$", "", block)
    block = re.sub(r"^\[?Fetching opaque proofs[^\n]*\n?", "", block, flags=re.M)
    return "\n".join(line.rstrip() for line in block.strip().splitlines())


def logical_axioms(text):
    if text.strip() == "Closed under the global context":
        return set()
    assert text.strip().startswith("Axioms:"), "Unrecognized assumption output"
    names = re.findall(r"^([\w.]+)\s*:", text, re.M)
    names = [n for n in names if n != "Axioms"]
    assert names and len(names) == len(set(names)), "Unparsed/duplicate logical assumptions"
    # Every unindented nonempty line after the header must start a declaration.
    for line in text.splitlines()[1:]:
        assert not line or line[0].isspace() or re.match(r"^[\w.]+\s*:", line), line
    return set(names)


def parse(result, endpoints):
    assert result.returncode == 0 and not re.search(r"\bError:", result.stderr + result.stdout), \
        "Coq endpoint audit failed:\n" + result.stderr + result.stdout
    answers = []
    for i, endpoint in enumerate(endpoints):
        for kind in ("TYPE", "AXIOMS", "END"):
            assert len(re.findall(rf"^AUDIT_{kind}_{i}$", result.stdout, re.M)) == 1, \
                "Missing/duplicate audit marker: " + endpoint
        match = re.search(rf"AUDIT_TYPE_{i}\n(.*?)AUDIT_AXIOMS_{i}\n(.*?)AUDIT_END_{i}\n", result.stdout, re.S)
        assert match, "Malformed marker order: " + endpoint
        typ, assumptions = map(clean, match.groups())
        assert typ and ':' in typ, "Missing type: " + endpoint
        logical_axioms(assumptions)
        answers.append({"name": endpoint, "type": typ, "assumptions": assumptions})
    return answers


def declaration_module(endpoint):
    """Require the source library, not a nested Rocq module inside it."""
    parts = endpoint.split('.')
    if parts[0] == 'PTree':
        for end in range(len(parts) - 1, 1, -1):
            source = ROOT.joinpath('theories', *parts[1:end]).with_suffix('.v')
            if source.is_file():
                return '.'.join(parts[:end])
    # Unknown/foreign references still reach Rocq's checked error protocol.
    return endpoint.rsplit('.', 1)[0]


def query(endpoints, modules=None):
    assert len(endpoints) == len(set(endpoints)), "Duplicate endpoint"
    modules = sorted(set(modules or [declaration_module(n) for n in endpoints]))
    commands = ["Require " + m + "." for m in modules]
    commands += ["Set Printing Width 100.", "Set Printing Depth 1000.", "Set Printing Implicit."]
    for i, name in enumerate(endpoints):
        for kind, command in [("TYPE", "Check @" + name), ("AXIOMS", "Print Assumptions " + name), ("END", None)]:
            commands.append(f'Goal True. idtac "AUDIT_{kind}_{i}". Abort.')
            if command:
                commands.append(command + ".")
    result = subprocess.run(["opam", "exec", "--", "coqtop", "-quiet", "-R", "_build/default/theories", "PTree"],
                            input='\n'.join(commands)+'\n', text=True, capture_output=True, cwd=ROOT)
    return parse(result, endpoints)


def compare(expected, actual):
    assert len(expected) == len(actual), "Endpoint count changed"
    assert len({e['name'] for e in expected}) == len(expected), "Duplicate manifest endpoint"
    assert expected == actual, "Compiled type/assumption drift: " + str([
        e['name'] for e, a in zip(expected, actual) if e != a])


def check(scope=None):
    data = json.loads(MANIFEST.read_text())
    entries = data['endpoints']
    if scope:
        entries = [e for e in entries if e['name'] in data[scope]]
    actual = query([e['name'] for e in entries], data['modules'])
    compare(entries, actual)
    for e in actual:
        if e['name'] in data['soundness']:
            assert logical_axioms(e['assumptions']) <= SOUNDNESS_AXIOMS, e['name']
    print(f"{len(actual)} exact compiled contracts and per-endpoint assumptions unchanged.")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='check (also the default)')
    parser.add_argument('--scope', choices=['api', 'soundness'])
    args = parser.parse_args()
    check(args.scope)
