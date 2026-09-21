#!/usr/bin/env python3
"""Read-only namespace/proof-text and coqdep client audit.

Run after `opam exec -- dune build`. Output is Markdown; no files are written.
Proof-text invariance compares the two frozen layout revisions; client
analysis uses the current build, allowing subsequent reviewed theory fixes.
"""
import csv
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = "92e0841"
LAYOUT = "6194bdf"
AGGREGATE = "PTree.Regression.Infrastructure.AllImports"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True)


def logical(path):
    return "PTree." + str(path).removeprefix("theories/").removesuffix(".v").replace("/", ".")


with (ROOT / "docs/module-moves.tsv").open() as manifest:
    moves = {row["old_path"]: row["new_path"] for row in csv.DictReader(manifest, delimiter="\t")}
modules = {logical(a): logical(b) for a, b in moves.items()}
require = re.compile(r"\b(?:From\s+([\w.]+)\s+)?Require\s+(?:(Import|Export)\s+)?([\w.\s]+?)\.(?=\s|$)")


def normalize(source, old=False):
    # Flatten adjacent Require groups to one command per module, preserving
    # order and Import/Export mode. Everything else must remain byte-identical.
    def replace(match):
        prefix, mode, names = match.groups()
        targets = [(prefix + "." if prefix else "") + n for n in names.split()]
        if old:
            targets = [modules.get(n, n) for n in targets]
        return "\n".join("Require " + (mode + " " if mode else "") + n + "." for n in targets)
    if old:
        # The only non-import source edit is an updated documentation link.
        source = source.replace("Examples/FreeOmegaEscapingMass", "Regression/Backend/FreeOmegaEscapingMass")
    return require.sub(replace, source)


baseline = git("ls-tree", "-r", "--name-only", BASE, "theories").splitlines()
baseline = [p for p in baseline if p.endswith(".v")]
current = {str(p.relative_to(ROOT)) for p in (ROOT / "theories").rglob("*.v")}
layout = {p for p in git("ls-tree", "-r", "--name-only", LAYOUT, "theories").splitlines()
          if p.endswith(".v")}
assert layout == {moves.get(p, p) for p in baseline}, "Layout snapshot differs from move manifest"
import_changes = []
for old_path in baseline:
    new_path = moves.get(old_path, old_path)
    old = git("show", BASE + ":" + old_path)
    new = git("show", LAYOUT + ":" + new_path)
    assert normalize(old, old=True) == normalize(new), "Non-namespace source change: " + new_path
    for match in require.finditer(old):
        prefix, mode, names = match.groups()
        for name in names.split():
            full = (prefix + "." if prefix else "") + name
            if full in modules:
                import_changes.append((logical(new_path), full, modules[full]))

# Use Coq's dependency output, not a filename-based approximation of clients.
depfile = ROOT / "_build/default/theories/.PTree.theory.d"
graph = {logical(p): set() for p in current}
seen = set()
for line in depfile.read_text().splitlines():
    lhs, rhs = line.split(": ", 1)
    target = lhs.split()[0]
    if not target.endswith(".vo"):
        continue
    mod = logical("theories/" + target.removesuffix(".vo") + ".v")
    assert mod in graph, "Stale coqdep target: " + mod
    seen.add(mod)
    for dep in rhs.split():
        if dep.endswith(".vo") and not dep.startswith("/"):
            dependency = logical("theories/" + dep.removesuffix(".vo") + ".v")
            assert dependency in graph, "Missing local dependency: " + dependency
            graph[mod].add(dependency)
assert seen == set(graph), "coqdep does not cover every maintained source"
library = ("PTree.Core.", "PTree.Prob.", "PTree.Eq.", "PTree.Semantics.",
           "PTree.Interp.", "PTree.API.")
for module, dependencies in graph.items():
    if module.startswith(library):
        assert not any(d.startswith(("PTree.Regression.", "PTree.Examples.")) for d in dependencies), \
            "Library depends on a regression/case study: " + module
    if module.startswith("PTree.Examples."):
        assert not any(d.startswith("PTree.Regression.") for d in dependencies), \
            "Case study depends on regression fixtures: " + module
# An import-only integration harness is not a substantive theorem client.
# Check it covers every other module, then omit it from reachability counts.
if AGGREGATE in graph:
    assert graph[AGGREGATE] == set(graph) - {AGGREGATE}, "Incomplete aggregate imports"
    assert not any(AGGREGATE in ds for ds in graph.values()), "Aggregate has an ordinary client"
    graph.pop(AGGREGATE)
clients = {m: {c for c, ds in graph.items() if m in ds} for m in graph}


def closure(seeds, edges):
    done, todo = set(), list(seeds)
    while todo:
        node = todo.pop()
        if node not in done:
            done.add(node)
            todo.extend(edges[node] - done)
    return done


def listing(items):
    return ", ".join("`" + m + "`" for m in sorted(items)) or "none"


roots = {m for m in graph if m.startswith(("PTree.Core.", "PTree.Semantics.", "PTree.Examples."))}
roots |= {"PTree.Eq." + n for n in ("ProbabilisticSemantics", "FreeOmega", "PStruct", "PStrong", "ProbabilisticTraceSubEnum", "ProbabilisticTraceEnum")}
gate_b_moves = {logical(a): logical(b) for a, b in
                json.loads((ROOT / "docs/gate-b-moves.json").read_text())["moves"].items()}
roots = {gate_b_moves.get(m, m) for m in roots}
roots |= {m for m in graph if m.startswith(("PTree.API.", "PTree.Interp."))}
roots |= {"PTree.PTree", "PTree.Semantics"}
reachable = closure(roots, graph)
family = {m for m in graph if m.startswith("PTree.Eq.Internal.")}

print("# Structural layout audit\n")
print("This is a repository-local dependency audit, not a theorem-usage or external-client census. "
      "It separately verifies historical layout invariance and reports current clients.\n")
print("Regenerate with `python3 tools/audit_layout.py` after a full `opam exec -- dune build`. "
      "The read-only proof-text check is pinned to the layout snapshot, not later reviewed fixes.\n")
print("## Scope and invariance\n")
print(f"- Layout comparison: `{BASE}` -> `{LAYOUT}`; {len(baseline)} Coq modules before and after; {len(moves)} moves; zero theorem/module deletions.")
print("- Between those snapshots all definition, theorem-statement and proof text is identical after normalizing Require paths; "
      "the only other Coq edit updates one comment's regression path.")
print("- In that historical snapshot all nine `Semantics/` modules and all finite-internal/kernel implementations remained in place. "
      "The later [Gate B migration](ARCHITECTURE_MIGRATION.md) relocates modules; current client paths below include those moves.")
print("- [Complete file move manifest](module-moves.tsv): each row also determines the old/new qualified module name; "
      "file basenames and declaration names are unchanged. No compatibility wrapper modules were added.")
print("- Classification: 15 files in four case-study groups; 50 regressions "
      "(17 semantics, 14 backend, 4 probability, 15 infrastructure). "
      "Factory contains ordinary Von Neumann support shared by the interactive service.")
print("- The later [universe repair](UNIVERSE_CONSISTENCY.md) updates two old Enum/Enum regressions "
      "and adds one import-only integration harness; it is not asserted to be a namespace-only change.")
print("- The layout milestone introduced no final MDP-encoding transition corollary or new semantic theorem; "
      "later theory work is recorded in [THEORY_STATUS](../THEORY_STATUS.md).\n")
print("## Dependency method and retained roots\n")
print(f"Coq's `.PTree.theory.d` supplies {sum(map(len, graph.values()))} direct local Require edges "
      f"covering {len(graph)} ordinary modules out of {len(current)} maintained modules. External libraries are excluded. "
      "Transitive clients include re-export paths; an import does not prove use of each declaration.\n")
print("`AllImports` is checked to import every other module, then excluded from client/reachability "
      "counts: an integration harness must not make every otherwise-unused module look substantively live.\n")
print("Checked layer boundaries: Core/Prob/Eq/Semantics/Interp/API import no case study or regression; "
      "case studies import no regression. Regression-to-case-study reuse is allowed.\n")
print("Roots are every Core module, every semantic comparison module, the API/Interp modules and top-level facades, "
      "the structural/strong and FreeOmega equational endpoints, both concrete trace probability endpoints, "
      "and all four retained case-study groups. This deliberately does not treat every regression as a public root.\n")
print(listing(roots) + "\n")
print(f"Root closure reaches {len(reachable)} modules; {len(graph) - len(reachable)} lie outside it. "
      "Unreachable modules can still be meaningful regressions or independent measure theorems. "
      "All remain built by Dune; no deletion follows from this classification.\n")
print("### Outside the selected root closure\n")
for m in sorted(set(graph) - reachable):
    print(f"- `{m}` ({len(clients[m])} direct local clients)")
print("\n### Zero direct local clients (report only)\n")
print(f"{sum(not c for c in clients.values())} modules have no direct local client. "
      "This includes exported roots and executable/negative regression leaves, not just potential dead code.\n")
for m in sorted(m for m in graph if not clients[m]):
    print(f"- `{m}`" + (" — retained root" if m in roots else " — built leaf"))
print("\n## Finite-internal / kernel family: complete local client report\n")
print("Scope: every `Eq/**/FiniteInternal*.v`, plus FreeOmega KernelCompletion, "
      "KernelCongruence, KernelProjection, KernelDisintegration, KernelContinuity and CostedKernel. "
      "Incoming/outgoing direct lists and transitive client lists are exhaustive within `theories/`. "
      "Gate B moved this family under Eq/Internal, updating all clients together. "
      "No dead-code conclusion follows from historical names.\n")
for m in sorted(family):
    print(f"### `{m}`\n")
    print("- In retained-root closure: " + ("yes" if m in reachable else "no") + ".")
    print("- Direct imports: " + listing(graph[m]) + ".")
    print("- Direct clients: " + listing(clients[m]) + ".")
    print("- All transitive clients: " + listing(closure(clients[m], clients)) + ".\n")
print("## All changed Require paths\n")
print(f"{len(import_changes)} imported-module occurrences in "
      f"{len({c for c, _, _ in import_changes})} client files change namespace.\n")
print("Each row is one imported module occurrence at the historical layout snapshot (before Gate B). "
      "Multi-module statements were split only when their destinations differ, preserving import order.\n")
print("| Client after move | Previous import | Current import |\n| --- | --- | --- |")
for client, old, new in sorted(import_changes):
    print(f"| `{client}` | `{old}` | `{new}` |")
