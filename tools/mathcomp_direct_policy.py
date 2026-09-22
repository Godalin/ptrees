"""Exact Gate M exception. No prefix-based universe-checking permission."""
import re
from audit_assumptions import without_comments

DIRECT = 'Eq/Backend/MathComp/Direct'
GATE_M = frozenset({DIRECT, 'Regression/Backend/MathCompDirect'})
ALLOWLIST = frozenset('theories/' + m + '.v' for m in GATE_M)


def universe_source_check(path, text):
    code = re.sub(r'"(?:""|[^"\n])*"', '""', without_comments(text))
    approved = r'^\s*Local Unset Universe Checking\.\s*$'
    occurrences = list(re.finditer(approved, code, re.M))
    if path in ALLOWLIST:
        assert len(occurrences) == 1, 'Gate M requires exactly one explicit local bypass: ' + path
        code = re.sub(approved, '', code, flags=re.M)
        assert not re.search(r'\b(?:Class|Inductive|CoInductive|Fixpoint|CoFixpoint)\b', code), \
            'No new representation/capability in direct assembly/probes: ' + path
    assert not re.search(r'\b(?:Unset\s+(?:Universe|Guard|Positivity)\s+Checking|'
                         r'Universe\s+Checking|bypass_check|TypeInType)\b', code), \
        'Unapproved unsafe typing setting: ' + path


def check_gate_boundary(edges):
    """All safe modules (including tests/aggregates) have safe-only closures.

    Every M client depends on the explicit assembly. Testing every direct
    edge suffices for the transitive separation, even for indirect helpers.
    """
    assert GATE_M <= edges.keys(), 'Missing reviewed Gate M module'
    for module, deps in edges.items():
        assert module in GATE_M or not (deps & GATE_M), \
            'Gate S imports universe-unchecked module: ' + module
    for module in GATE_M - {DIRECT}:
        seen, todo = set(), [module]
        while todo:
            node = todo.pop()
            if node not in seen:
                seen.add(node)
                todo.extend(edges[node])
        assert DIRECT in seen, 'Gate M client does not use direct backend: ' + module


def safe_targets(root):
    return sorted(str(p.relative_to(root).with_suffix('.vo'))
                  for p in (root / 'theories').rglob('*.v')
                  if p.relative_to(root).as_posix() not in ALLOWLIST)


def check_build_flags(root):
    # No project-wide CLI bypass may evade the source-file exception.
    paths = [root / 'dune-project', root / '_CoqProject', root / '.coqrc']
    paths += list((root / 'theories').rglob('dune'))
    for path in paths:
        if path.exists():
            assert not re.search(r'-type-in-type|bypass_check|Unset\s+(?:Universe|Guard|Positivity)\s+Checking',
                                 path.read_text()), 'Unsafe project build setting: ' + str(path)
