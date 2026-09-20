#!/usr/bin/env python3
"""Report the cleanup inventory from current sources and Coq's dependency graph.

Read-only. Run dune build first; --check compares the checked-in baseline.
This records architectural debt rather than accepting it as the final layout.
It does not infer theorem use from imports or delete zero-client modules.
"""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
THEORIES = ROOT / "theories"
REPORT = ROOT / "docs/ARCHITECTURE_AUDIT.md"
AGGREGATE = "Regression/Infrastructure/AllImports"

# Reviewed ownership, not inferred semantic dependencies. Full output lists
# every module so --check catches additions, removals and classification drift.
INTERP = {
    "Eq/FreeOmega/Interp": "Interp/FreeOmega/Base",
    "Eq/FreeOmega/GuardedInterp": "Interp/FreeOmega/Guarded",
    "Semantics/AtomicInterp": "Interp/FreeOmega/Atomic",
    "Semantics/MDPInterp": "Interp/FreeOmega/MDP",
    "Semantics/MDPInterpSubEnum": "Interp/Backend/SubEnum",
}
GENERIC_PROB = {
    "TwoLevelMeasure", "Coupling", "IndexedCoupling", "RelLift",
    "SemanticCoupling", "FrontierLift", "MeasureIteration",
}
LEGACY_PROB = {"Monad", "MonadList", "Discrete"}
FINITE_SUPPORT = {
    "FinSupp", "FiniteCapacityMatching", "FiniteEnumPresentation",
    "FiniteEnumTransport", "FiniteMatching", "FiniteRationalTransport",
    "RatGeometric", "RatSubTypes", "RealSubTypes", "DiscreteMC",
}
KERNEL = {"KernelCompletion", "KernelCongruence", "KernelProjection",
          "KernelDisintegration", "KernelContinuity", "CostedKernel"}


def ownership(path):
    """(target area, specialization, disposition). No file move is performed."""
    name = path.rsplit("/", 1)[-1]
    if path in INTERP:
        return INTERP[path], ("SubEnum" if name.endswith("SubEnum") else "FreeOmega"), "move; freeze statements"
    if path == AGGREGATE:
        return "Regression/Infrastructure", "integration", "retain; exclude from client counts"
    if path.startswith("Regression/"):
        return path.rsplit("/", 1)[0], "contract test", "retain; not a public theory endpoint"
    if path.startswith("CaseStudies/"):
        return "CaseStudies", "application", "retain; audit raw-Enum qualifications separately"
    if path == "Experimental/UniverseSeparatedPTree":
        return "Regression/Infrastructure", "universe boundary", "reclassify checked probes; revise historical comments"
    if path.startswith("Experimental/"):
        raise AssertionError("An experiment needs an explicit disposition: " + path)
    if path == "Core/PTreeDefinition":
        return "Core", "syntax", "split legacy stuckM/MonadMeasure convenience from syntax"
    if path == "Core/PTreeProbability":
        return "Eq/WellFormedness", "generic", "move probability validity and closure proofs"
    if path in {"Core/PTreeEnum", "Core/PTreeSubEnum"}:
        return "API/" + name.removeprefix("PTree"), "tree/backend adapter", "move; not measure-only infrastructure"
    if path.startswith("Core/"):
        return "Core", "syntax utility", "retain"
    if path == "Prob/EnumCofinality":
        return "Eq/Backend/EnumCofinality", "Enum", "move; contains tree bind-scheduling theorems"
    if path.startswith("Prob/FreeOmega"):
        if name.endswith(("Enum", "SubEnum", "EnumAudit")):
            return "Prob/Backend/FreeOmega", "SubEnum" if "SubEnum" in name else "Enum", "group concrete realization proofs"
        return "Prob/FreeOmega", "FreeOmega", "group; measure infrastructure, not tree equality"
    if path.startswith("Prob/"):
        if name in GENERIC_PROB:
            return "Prob/Interface", "generic", "retain capability infrastructure; distinguish legacy adapters"
        if name in LEGACY_PROB:
            return "Prob/Legacy", "weighted legacy", "quarantine; check clients before any deletion"
        if name in FINITE_SUPPORT or "Enum" in name or "MathComp" in name:
            return "Prob/Backend", "MathComp" if "MathComp" in name else "finite/real support", "group concrete infrastructure"
        raise AssertionError("Unclassified probability module: " + path)
    if path.startswith("Eq/"):
        if name.startswith("FiniteInternal") or name in KERNEL:
            return "Eq/Internal" + ("/FreeOmega" if "/FreeOmega/" in path else ""), "proof infrastructure", "retain pending client audit; not an equality relation"
        if path == "Eq/FreeOmega":
            return "API/FreeOmega", "expert export", "split canonical facade from implementation exports"
        if name == "ProbabilisticSemantics":
            return "API/Generic", "curated facade", "retain curated names; strengthen negative import tests"
        if path in {"Eq/FreeOmega/Base", "Eq/FreeOmega/Bind"}:
            return "Eq/FreeOmega + Interp/FreeOmega", "mixed responsibility", "split translation/interp sections; audit concrete imports"
        if name in {"ProbabilisticTraceEnum", "ProbabilisticTraceSubEnum"}:
            return "Eq/Backend", "SubEnum" if name.endswith("SubEnum") else "Enum", "concrete finite-cylinder endpoint"
        return path.rsplit("/", 1)[0], "FreeOmega" if "/FreeOmega/" in path else "generic", "retain canonical/equational theory"
    if path.startswith("Semantics/"):
        profile = "FreeOmega" if name.endswith("FreeOmega") else "SubEnum" if name.endswith("SubEnum") else "generic"
        # Fixing MF := FreeOmega MN still leaves the native model generic.
        # Only a concrete native carrier belongs under Backend.
        area = "Semantics/FreeOmega" if profile == "FreeOmega" else "Semantics/Backend" if profile == "SubEnum" else "Semantics"
        return area, profile, "retain comparison semantics; not canonical equality"
    raise AssertionError("Module needs an explicit architectural owner: " + path)


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
    for mod, ds in edges.items():
        if mod.split("/")[0] in {"Core", "Prob", "Eq", "Semantics", "Interp", "API"}:
            assert not any(d.startswith(("Regression/", "CaseStudies/", "Experimental/")) for d in ds), "Library depends on tests/experiments: " + mod
        if mod.startswith("CaseStudies/"):
            assert not any(d.startswith(("Regression/", "Experimental/")) for d in ds), "Case study depends on tests/experiments: " + mod
    return edges


def report():
    edges = graph()
    ordinary = set(edges) - {AGGREGATE}
    clients = {m: {c for c in ordinary if m in edges[c]} for m in edges}
    rows = []
    def out(line=""):
        rows.append(line)
    def names(xs):
        return ", ".join("`" + x + "`" for x in sorted(xs)) or "none"
    out("# Repository architecture baseline audit")
    out()
    out("Generated by `python3 tools/audit_architecture.py` after `opam exec -- dune build`. "
        "Check with `--check`. Paths omit `theories/` and `.v`.")
    out()
    out("This is the **pre-migration inventory**, not a completed cleanup or an adequacy proof. "
        "Ownership is a reviewed classification; dependencies are Coq's actual Require graph. "
        "Importing a module does not establish use of every theorem in it. "
        "Target areas are design decisions, not existing imports or compatibility promises.")
    out()
    out(f"- {len(edges)} modules, {sum(map(len, edges.values()))} direct local edges including AllImports.")
    out(f"- {len(ordinary)} ordinary modules; AllImports is checked then excluded from client counts.")
    out("- Enforced: no maintained library imports Regression, CaseStudies or Experimental; "
        "no CaseStudy imports Regression or Experimental.")
    out("- Not claimed: theorem-use liveness, mathematical minimality, or completed public-API isolation.")
    out()
    out("## Concrete layering debts")
    out()
    out("These are reported obligations, not silently whitelisted as the final architecture.")
    out()
    for m in sorted(ordinary):
        bad = {d for d in edges[m] if
               (m.startswith("Core/") and not d.startswith("Core/")) or
               (m.startswith("Prob/") and not d.startswith(("Prob/", "Core/"))) or
               (m.startswith("Eq/") and m not in INTERP and d in INTERP)}
        if bad:
            out(f"- `{m}` -> {names(bad)}")
    out()
    out("## Inventory and disposition (every module)")
    out()
    out("| Current module | Target owner/area | Profile | Disposition | Ordinary direct clients |")
    out("| --- | --- | --- | --- | ---: |")
    for m in sorted(edges):
        area, profile, action = ownership(m)
        out(f"| `{m}` | `{area}` | {profile} | {action} | {len(clients[m])} |")
    out()
    out("## Finite-internal and kernel family: direct clients")
    out()
    out("These modules implement execution certificates, schedules and hitting adequacy. "
        "They do not resurrect `pfinite`. Zero clients is a review lead, not deletion authority. "
        "Regression-only clients are separated from substantive library/case-study clients.")
    out()
    for m in sorted(ordinary):
        if not m.startswith("Eq/") or not (m.rsplit("/", 1)[-1].startswith("FiniteInternal") or m.rsplit("/", 1)[-1] in KERNEL):
            continue
        test = {c for c in clients[m] if c.startswith("Regression/")}
        out(f"- `{m}`: library/application clients {names(clients[m] - test)}; regression clients {names(test)}.")
    out()
    out("## Experimental disposition")
    out()
    out("`UniverseSeparatedPTree` has only the aggregate harness as an incoming import. "
        "Its `Fail` commands test sealed MathComp universe obstructions and its positive "
        "declarations test alternative representations. Treat it as an infrastructure "
        "regression candidate, not a second supported PTree model. Before moving, replace "
        "the historical suggestion that the canonical two-level model still needs this "
        "migration; preserve the tested negative boundaries. No adequacy claim follows.")
    return "\n".join(rows) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = report()
    if args.check:
        if not REPORT.exists() or REPORT.read_text() != result:
            raise SystemExit("Architecture baseline differs; review the generated report before updating it.")
        print("Architecture inventory and dependency baseline match (all modules classified).")
    else:
        print(result, end="")
