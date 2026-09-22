#!/usr/bin/env python3
"""Read-only post-migration ownership/dependency audit. Run dune build first."""
import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
THEORIES = ROOT / "theories"
REPORT = ROOT / "docs/ARCHITECTURE_AUDIT.md"
AGGREGATE = "Regression/Infrastructure/AllImports"
INTERNAL_REASON = (
    "maintained execution/scheduling contract; private, not another equality"
)


def external_validation(path):
    """Independent domain and the explicitly planned one-way adapters.

    Classify adapters before they exist so a future soundness file cannot
    silently enter the mainline through an otherwise ordinary Backend edge.
    """
    return path.startswith(("Prob/Domain/", "Prob/FreeOmega/Validation/")) or path in {
        "Prob/Backend/Common/DomainTransport",
        "Prob/Backend/Common/CountableCoupling",
        "Prob/Backend/SubEnum/Domain", "Prob/Backend/MathComp/Domain",
        "Prob/Backend/SubEnumR/Domain",
        "Prob/Backend/SubEnumR/FreeOmega/Validation",
        "Prob/Backend/SubEnumR/FreeOmega/RelationalValidation",
        "Prob/Backend/SubEnumR/FreeOmega/JointRealization",
        "Prob/Backend/SubEnum/FreeOmega/Admissibility",
        "Prob/Backend/SubEnum/FreeOmega/DomainSoundness",
        "Prob/Backend/SubEnum/FreeOmega/QuotientSoundness",
        "Prob/Backend/SubEnum/FreeOmega/CountableSupport",
        "Prob/Backend/SubEnum/FreeOmega/CouplingSoundness",
        "Prob/Backend/SubEnum/FreeOmega/JointSoundness",
        "Prob/Backend/SubEnum/FreeOmega/GenericValidation",
        "Prob/Backend/SubEnum/FreeOmega/RelationalValidation",
        "Eq/Backend/StableHittingDomainSubEnum",
    }


def ownership(path):
    if path.startswith(("CaseStudies/", "Events/")):
        raise AssertionError("Unsupported top-level namespace: " + path)
    if path in {"PTree", "Semantics"}:
        return "API", "curated facade", "explicit user entry point; no implementation exports"
    if path.startswith("Experimental/"):
        raise AssertionError("Unreviewed experiment: " + path)
    if path == AGGREGATE:
        return "Regression/Infrastructure", "integration", "exclude from substantive clients"
    if path.startswith("Regression/Fixtures/"):
        return "Regression/Fixtures", "private test fixture", "shared samples only; no final regression dependency"
    if path.startswith("Regression/"):
        return path.rsplit("/", 1)[0], "contract test", "retained; not public theory"
    if path.startswith("Examples/"):
        return "Examples", "application", "retained; no regression dependency"
    if path.startswith("Prob/FreeOmega/Validation/"):
        return "Prob/FreeOmega/Validation", "external validation", "native-parametric bridge to independent mathematical models"
    if path.startswith("Core/"):
        return "Core", "syntax", "primitive syntax/combinators only"
    if path.startswith("API/"):
        return "API", "curated endpoint/adapter", "explicit assembly; no bulk export"
    if path.startswith("Prob/Backend/"):
        parts = path.split("/")
        assert len(parts) >= 4 and parts[2] in {"Common", "Enum", "SubEnum", "SubEnumR", "MathComp"}, "Ungrouped concrete probability module: " + path
        family = parts[2]
        owner = "/".join(parts[:3])
        if path in {"Prob/Backend/Common/DomainTransport", "Prob/Backend/Common/CountableCoupling"}:
            return owner, "external validation", "one-way adapter: independent real transport to expectation-domain joints"
        if family == "Common":
            return owner, "shared arithmetic/combinatorics", "no native carrier specialization"
        if len(parts) >= 5 and parts[3] == "FreeOmega":
            return owner + "/FreeOmega", family, "FreeOmega over a concrete native carrier, not generic FreeOmega MN"
        return owner, family, "native representation, laws or realization adapters"
    for prefix, profile, disposition in (
        ("Prob/Domain", "external validation", "independent mathematical domain; not a free completion or mainline premise"),
        ("Prob/Interface", "generic", "operation/law interfaces"),
        ("Prob/FreeOmega", "FreeOmega", "canonical measure model, not a concrete native backend"),
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
    if external_validation(dependency) and not (
            external_validation(module) or module.startswith("Regression/")):
        return False
    if module.startswith("Prob/Domain/"):
        return under("Prob/Domain")
    if module.startswith("Prob/FreeOmega/Validation/"):
        return under("Prob/Domain", "Prob/Interface", "Prob/FreeOmega")
    if module in {"Prob/Backend/Common/DomainTransport", "Prob/Backend/Common/CountableCoupling"}:
        return under("Prob/Domain", "Prob/Backend/Common")
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
    if module.startswith("Prob/Backend/Common/"):
        return under("Prob/Interface", "Prob/Backend/Common")
    if module.startswith("Prob/Backend/MathComp/"):
        return under("Prob/Interface", "Prob/FreeOmega", "Prob/Backend/Common", "Prob/Backend/MathComp", "Prob/Domain")
    if module.startswith("Prob/Backend/SubEnumR/"):
        if module == "Prob/Backend/SubEnumR/RationalEmbedding":
            return under("Prob/Backend/SubEnumR", "Prob/Backend/SubEnum",
                         "Prob/Backend/Enum", "Prob/Backend/Common")
        return under("Prob/Interface", "Prob/FreeOmega", "Prob/Backend/Common",
                     "Prob/Backend/SubEnumR", "Prob/Domain")
    if module.startswith(("Prob/Backend/Enum/", "Prob/Backend/SubEnum/")):
        # SubEnum is a validated Enum carrier, not an unrelated implementation.
        # Realization/observation adapters legitimately cross this boundary.
        return under("Prob/Interface", "Prob/FreeOmega", "Prob/Backend/Common",
                     "Prob/Backend/Enum", "Prob/Backend/SubEnum", "Prob/Legacy", "Prob/Domain")
    if module.startswith("Prob/Legacy/"):
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
    if module.startswith("Examples/"):
        return not under("Regression", "Experimental")
    if module.startswith("Regression/"):
        if module.startswith("Regression/Fixtures/") and dependency.startswith("Regression/"):
            return dependency.startswith("Regression/Fixtures/")
        return True
    return False


def closure(edges, roots):
    seen, todo = set(), list(roots)
    while todo:
        module = todo.pop()
        if module not in seen:
            seen.add(module)
            todo.extend(edges[module])
    return seen


def check_auxiliary_boundary(edges):
    # Formal theory/facades, not the regression fixtures used to test them.
    roots = {m for m in edges if m.startswith(("Interp/", "API/"))}
    roots |= {"Eq/PEutt", "PTree", "Semantics"}
    internal = {m for m in closure(edges, roots) if m.startswith("Eq/Internal/")}
    assert not internal, "Formal mainline depends on auxiliary internal machinery: " + str(sorted(internal))


def check_external_validation_boundary(edges):
    # Explicit validation adapters can live under Eq/Backend; they validate
    # reasoning and must not themselves be counted as reasoning roots.
    roots = {m for m in edges if not external_validation(m) and m.startswith(
        ("Core/", "Eq/", "Semantics/", "Interp/", "API/", "Examples/"))}
    roots |= {m for m in ("PTree", "Semantics") if m in edges}
    leaked = {m for m in closure(edges, roots) if external_validation(m)}
    assert not leaked, "Mainline depends on external validation: " + str(sorted(leaked))


def check_native_expectation_boundary(edges):
    # Native SubEnum validation precedes formal omega completion, even through
    # indirect finite-helper imports. Upper evaluators may use finite facts,
    # but finite facts must never depend on external validation in return.
    roots = {m for m in ("Prob/Backend/SubEnum/Expectation",
                         "Prob/Backend/SubEnum/Domain", "Prob/Backend/SubEnumR/Domain",
                         "Prob/Backend/SubEnumR/Representation", "Prob/Backend/SubEnumR/Measure") if m in edges}
    leaked = {m for m in closure(edges, roots) if "/FreeOmega/" in m}
    assert not leaked, "Native expectation/domain depends on FreeOmega: " + str(sorted(leaked))
    finite = "Prob/Backend/SubEnum/Expectation"
    if finite in edges:
        leaked = {m for m in closure(edges, {finite}) if external_validation(m)}
        assert not leaked, "Finite expectation depends on validation: " + str(sorted(leaked))


def aggregate_check(actual=None, expected=None):
    if expected is None:
        expected = sorted('PTree.' + p.relative_to(THEORIES).with_suffix('').as_posix().replace('/', '.')
                          for p in THEORIES.rglob('*.v')
                          if p != THEORIES / (AGGREGATE + '.v'))
    if actual is None:
        actual = re.findall(r'^Require (PTree\.[\w.]+)\.$',
                            (THEORIES / (AGGREGATE + '.v')).read_text(), re.M)
    assert actual == sorted(set(expected)), 'AllImports must contain every other module exactly once, sorted'


def graph():
    aggregate_check()
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
    check_auxiliary_boundary(edges)
    check_external_validation_boundary(edges)
    check_native_expectation_boundary(edges)
    return edges


def report():
    edges = graph()
    ordinary = set(edges) - {AGGREGATE}
    clients = {m: {c for c in ordinary if m in edges[c]} for m in edges}
    q = lambda s: chr(96) + s + chr(96)
    names = lambda xs: ", ".join(q(x) for x in sorted(xs)) or "none"
    rows = [
        "# Repository architecture: current ownership inventory", "",
        "Generated by " + q("python3 tools/audit_architecture.py") + " after a full build; compare with " + q("--check") + ".",
        "See [architecture policy](ARCHITECTURE.md); migration-stage inventories live in git history.", "",
        f"- {len(edges)} modules; {sum(map(len, edges.values()))} direct local Require edges.",
        f"- AllImports covers all {len(ordinary)} other modules and is excluded from client counts.",
        "- Every edge is checked against the ownership policy, not merely displayed as debt.",
        "- Core has no local probability dependency; Prob has no tree-theory dependency.",
        "- Generic interfaces and FreeOmega measure infrastructure import no concrete backend.",
        "- Concrete probability modules name Common/Enum/SubEnum/SubEnumR/MathComp ownership; Common cannot import a native carrier.",
        "- Native SubEnum expectation/domain closures exclude FreeOmega; finite expectation also excludes external validation.",
        "- MathComp and Enum/SubEnum do not depend on each other; Enum/SubEnum realization adapters may reuse each other.",
        "- Eq imports no Interp/Semantics/API; Semantics imports no Interp/API.",
        "- Generic/canonical-model Eq, Semantics and Interp modules import no concrete backend endpoint.",
        "- No maintained library imports Regression, Examples or Experimental.",
        "- Cases do not depend on tests. Experimental has no remaining source module.", "",
        "- The peutt/Interp/public-facade dependency closure contains no Eq/Internal module.", "",
        "- Prob/Domain depends only on mathematical libraries and itself, never the existing probability interfaces or FreeOmega.",
        "- The Core/Eq/Semantics/Interp/API/Examples and facade dependency closures exclude external validation; explicit validation adapters are not reasoning roots.", "",
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
             "FiniteInternal is auxiliary proof infrastructure for well-founded internal compression "
             "and related adequacy arguments. It is not part of the canonical PTree semantics or "
             "public equivalence theory. Members remain maintained independent infrastructure; completed "
             "SubEnum domain soundness does not use this branch. Regression-only leaves "
             "are retained as checked execution, coupling, schedule or recovery contracts; none "
             "is re-exported as a public equality. No theorem deletion is inferred from client counts.", ""]
    rows += ["The formal peutt/Interp/facade mainline has no transitive Eq/Internal dependency. "
             "Some Stage 1-4 regressions do load it via Regression/Probability/CorrelatedSampleAlgebra; "
             "this is a fixture import, not evidence that the formal preservation theorems need it. "
             "Cleanup does not redesign or delete this auxiliary API merely because the final "
             "soundness proof does not depend on it.", ""]
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
    parser.add_argument("--aggregate-only", action="store_true")
    args = parser.parse_args()
    if args.aggregate_only:
        aggregate_check()
        print('AllImports coverage/order/uniqueness passed (no build required).')
        raise SystemExit(0)
    result = report()
    if args.check:
        if not REPORT.exists() or REPORT.read_text() != result:
            raise SystemExit("Architecture report differs; review before updating.")
        print("All module ownership/dependency constraints and the checked report agree.")
    else:
        print(result, end="")
