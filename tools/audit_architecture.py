#!/usr/bin/env python3
"""Read-only post-migration ownership/dependency audit. Run dune build first."""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
THEORIES = ROOT / "theories"
REPORT = ROOT / "docs/ARCHITECTURE_AUDIT.md"
AGGREGATE = "Regression/Infrastructure/AllImports"
INTERNAL_REASON = (
    "maintained execution/scheduling contract; private, not another equality"
)


def ownership(path):
    if path in {"PTree", "Semantics"}:
        return "API", "curated facade", "explicit user entry point; no implementation exports"
    if path.startswith("Experimental/"):
        raise AssertionError("Unreviewed experiment: " + path)
    if path == AGGREGATE:
        return "Regression/Infrastructure", "integration", "exclude from substantive clients"
    if path.startswith("Regression/"):
        return path.rsplit("/", 1)[0], "contract test", "retained; not public theory"
    if path.startswith("CaseStudies/"):
        return "CaseStudies", "application", "retained; no regression dependency"
    if path.startswith("Core/"):
        return "Core", "syntax", "primitive syntax/combinators only"
    if path.startswith("API/"):
        return "API", "curated endpoint/adapter", "explicit assembly; no bulk export"
    for prefix, profile, disposition in (
        ("Prob/Interface", "generic", "operation/law interfaces"),
        ("Prob/FreeOmega", "FreeOmega", "canonical measure model, not a concrete native backend"),
        ("Prob/Backend", "concrete", "measure implementation or specialized realization"),
        ("Prob/Legacy", "weighted legacy", "explicit retained clients; not canonical probability"),
        ("Eq/Internal/Backend", "concrete", INTERNAL_REASON),
        ("Eq/Internal/FreeOmega", "FreeOmega", INTERNAL_REASON),
        ("Eq/Internal", "generic", INTERNAL_REASON),
        ("Eq/Backend", "concrete", "tree equations/quantitative endpoints for concrete carriers"),
        ("Eq/FreeOmega", "FreeOmega", "canonical-model equational theory"),
        ("Eq", "generic", "canonical equivalence, validity and hitting algebra"),
        ("Semantics/Backend", "SubEnum", "retain comparison semantics; not canonical equality"),
        ("Semantics/FreeOmega", "FreeOmega", "retain comparison semantics; not canonical equality"),
        ("Semantics", "generic", "independent comparison semantics"),
        ("Interp/Backend", "SubEnum", "concrete interpreter endpoint"),
        ("Interp/FreeOmega", "FreeOmega", "canonical-model interpreter compositionality"),
        ("Interp", "generic", "structural interpretation or generic hitting infrastructure"),
    ):
        if path.startswith(prefix + "/"):
            return prefix, profile, disposition
    raise AssertionError("Module lacks an architectural owner: " + path)


def permitted(module, dependency):
    def under(*prefixes):
        return any(dependency.startswith(p + "/") for p in prefixes)
    # A generic theorem layer may not silently fix its observable carrier.
    if ownership(module)[1] == "generic" and ownership(dependency)[1] == "FreeOmega":
        return False
    if module == "PTree":
        return under("API")
    if module == "Semantics":
        return under("Semantics")
    if module.startswith("Core/"):
        return under("Core")
    if module.startswith("Prob/Interface/"):
        return under("Prob/Interface")
    if module.startswith("Prob/FreeOmega/"):
        return under("Prob/Interface", "Prob/FreeOmega")
    if module.startswith(("Prob/Backend/", "Prob/Legacy/")):
        return under("Prob")
    if module.startswith("Eq/"):
        ok = under("Core", "Prob", "Eq")
        if "/Backend/" not in module:
            ok = ok and not under("Prob/Backend", "Prob/Legacy", "Eq/Backend", "Eq/Internal/Backend")
        return ok
    if module.startswith("Semantics/"):
        ok = under("Core", "Prob", "Eq", "Semantics")
        if "/Backend/" not in module:
            ok = ok and not under("Prob/Backend", "Prob/Legacy", "Eq/Backend", "Eq/Internal/Backend", "Semantics/Backend")
        return ok
    if module.startswith("Interp/"):
        ok = under("Core", "Prob", "Eq", "Semantics", "Interp")
        if "/Backend/" not in module:
            ok = ok and not under("Prob/Backend", "Prob/Legacy", "Eq/Backend", "Eq/Internal/Backend", "Semantics/Backend", "Interp/Backend")
        return ok
    if module.startswith("API/"):
        return under("Core", "Prob", "Eq", "Semantics", "Interp", "API")
    if module.startswith("CaseStudies/"):
        return not under("Regression", "Experimental")
    if module.startswith("Regression/"):
        return True
    return False


def graph():
    paths = {p.relative_to(THEORIES).with_suffix("").as_posix() for p in THEORIES.rglob("*.v")}
    edges = {p: set() for p in paths}
    seen = set()
    for line in (ROOT / "_build/default/theories/.PTree.theory.d").read_text().splitlines():
        lhs, rhs = line.split(": ", 1)
        target = lhs.split()[0]
        if not target.endswith(".vo"):
            continue
        module = target.removesuffix(".vo")
        assert module in edges, "Stale coqdep target: " + module
        seen.add(module)
        for dep in rhs.split():
            if dep.endswith(".vo") and not dep.startswith("/"):
                name = dep.removesuffix(".vo")
                assert name in edges, "Missing dependency: " + name
                edges[module].add(name)
    assert seen == paths, "Run a full build: incomplete coqdep graph"
    assert edges[AGGREGATE] == paths - {AGGREGATE}, "Incomplete AllImports"
    assert all(AGGREGATE not in ds for ds in edges.values()), "Aggregate used as library"
    for module, deps in edges.items():
        ownership(module)
        for dep in deps:
            assert permitted(module, dep), "Forbidden ownership edge: " + module + " -> " + dep
    return edges


def report():
    edges = graph()
    ordinary = set(edges) - {AGGREGATE}
    clients = {m: {c for c in ordinary if m in edges[c]} for m in edges}
    q = lambda s: chr(96) + s + chr(96)
    names = lambda xs: ", ".join(q(x) for x in sorted(xs)) or "none"
    rows = [
        "# Repository architecture: Gate B audit", "",
        "Generated by " + q("python3 tools/audit_architecture.py") + " after a full build; compare with " + q("--check") + ".",
        "The accepted pre-migration inventory is [archived separately](ARCHITECTURE_BASELINE.md).", "",
        f"- {len(edges)} modules; {sum(map(len, edges.values()))} direct local Require edges.",
        f"- AllImports covers all {len(ordinary)} other modules and is excluded from client counts.",
        "- Every edge is checked against the ownership policy, not merely displayed as debt.",
        "- Core has no local probability dependency; Prob has no tree-theory dependency.",
        "- Generic interfaces and FreeOmega measure infrastructure import no concrete backend.",
        "- Eq imports no Interp/Semantics/API; Semantics imports no Interp/API.",
        "- Generic/canonical-model Eq, Semantics and Interp modules import no concrete backend endpoint.",
        "- No maintained library imports Regression, CaseStudies or Experimental.",
        "- Cases do not depend on tests. Experimental has no remaining source module.", "",
        "This is an import-graph check, not declaration-use liveness, capability minimality, "
        "FreeOmega adequacy, or the final whole-library kernel audit.", "",
        "## Complete module ownership", "",
        "| Module | Owner | Profile | Disposition | Ordinary clients |",
        "| --- | --- | --- | --- | ---: |",
    ]
    for module in sorted(edges):
        area, profile, disposition = ownership(module)
        rows.append(f"| {q(module)} | {q(area)} | {profile} | {disposition} | {len(clients[module])} |")
    rows += ["", "## Internal certificate/kernel disposition", "",
             "All members remain maintained proof infrastructure, now in Eq/Internal. "
             "Their declarations are covered by the migration text audit. Regression-only leaves "
             "are retained as checked execution, coupling, schedule or recovery contracts; none "
             "is re-exported as a public equality. No theorem deletion is inferred from client counts.", ""]
    for module in sorted(ordinary):
        if module.startswith("Eq/Internal/"):
            tests = {c for c in clients[module] if c.startswith("Regression/")}
            rows.append(f"- {q(module)}: ordinary theory/application clients {names(clients[module] - tests)}; regression clients {names(tests)}.")
    rows += ["", "## Experimental disposition", "",
             "UniverseSeparatedPTree is now a Regression/Infrastructure contract test. "
             "Its positive probes and checked Fail commands are retained; historical comments "
             "no longer describe the canonical FreeOmega representation as awaiting migration. "
             "No alternative representation is exported as maintained theory.", ""]
    return "\n".join(rows)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = report()
    if args.check:
        if not REPORT.exists() or REPORT.read_text() != result:
            raise SystemExit("Architecture report differs; review before updating.")
        print("All module ownership/dependency constraints and the checked report agree.")
    else:
        print(result, end="")
