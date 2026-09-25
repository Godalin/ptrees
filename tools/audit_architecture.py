#!/usr/bin/env python3
"""Read-only post-migration ownership/dependency audit. Run dune build first."""
import argparse
import re
from pathlib import Path
from audit_assumptions import without_comments
from mathcomp_direct_policy import GATE_M, check_gate_boundary

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
    return path.startswith(("Prob/Domain/", "Prob/FreeOmega/Validation/",
                            "Execution/Validation/")) or path in {
        "Prob/Backend/Common/DomainTransport",
        "Prob/Backend/Common/CountableCoupling",
        "Prob/Backend/Common/CountableRelationalLimit",
        "Prob/Backend/SubEnumQ/Domain", "Prob/Backend/MathComp/Domain",
        "Prob/Backend/SubEnumR/Domain",
        "Prob/Backend/SubEnumR/FreeOmega/Validation",
        "Prob/Backend/SubEnumR/FreeOmega/RelationalValidation",
        "Prob/Backend/SubEnumR/FreeOmega/NativeReflection",
        "Prob/Backend/SubEnumR/FreeOmega/CountableSupport",
        "Prob/Backend/SubEnumR/FreeOmega/JointRealization",
        "Prob/Backend/SubEnumQ/FreeOmega/Admissibility",
        "Prob/Backend/SubEnumQ/FreeOmega/DomainSoundness",
        "Prob/Backend/SubEnumQ/FreeOmega/QuotientSoundness",
        "Prob/Backend/SubEnumQ/FreeOmega/CountableSupport",
        "Prob/Backend/SubEnumQ/FreeOmega/CouplingSoundness",
        "Prob/Backend/SubEnumQ/FreeOmega/JointSoundness",
        "Prob/Backend/SubEnumQ/FreeOmega/GenericValidation",
        "Prob/Backend/SubEnumQ/FreeOmega/RelationalValidation",
        "Eq/Backend/StableHittingDomainSubEnumQ",
    }


def ownership(path):
    if path in GATE_M:
        return path.rsplit('/', 1)[0], 'universe-unchecked Gate M', 'direct MathComp assembly/probes; excluded from safe aggregate'
    if path.startswith(("CaseStudies/", "Events/", "API/")):
        raise AssertionError("Unsupported top-level namespace: " + path)
    if path in {"PTree", "Eq", "PTreeFacts", "Semantics"}:
        return "EntryPoint", "aggregate", "explicit syntax/relation/facts/comparison entry point"
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
    if path == "Execution/Validation/SubEnumQ":
        return "Execution/Validation", "external validation", "one-way runner-to-hitting correspondence; never an executable dependency"
    if path.startswith("Execution/Validation/"):
        return "Execution/Validation", "execution validation", "conditional sampler/replay probability laws; never an executable dependency"
    if path.startswith("Execution/Backend/"):
        return "Execution/Backend", "concrete", "executable native sampling; no external validation or recursive frontier"
    if path.startswith("Execution/"):
        return "Execution", "generic", "operational runner and finite path correctness; sampler laws are separate"
    if path.startswith("Prob/Backend/"):
        parts = path.split("/")
        assert len(parts) >= 4 and parts[2] in {"Common", "EnumQ", "SubEnumQ", "SubEnumR", "MathComp"}, "Ungrouped concrete probability module: " + path
        family = parts[2]
        assert not (family == "MathComp" and "FreeOmega" in parts[3:]), \
            "Removed MathComp completion namespace: " + path
        owner = "/".join(parts[:3])
        if path in {"Prob/Backend/Common/DomainTransport", "Prob/Backend/Common/CountableCoupling", "Prob/Backend/Common/CountableRelationalLimit"}:
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
        ("Semantics/Backend", "SubEnumQ", "retain comparison semantics; not canonical equality"),
        ("Semantics/FreeOmega", "FreeOmega", "retain comparison semantics; not canonical equality"),
        ("Semantics", "generic", "independent comparison semantics"),
        ("Interp/Backend", "SubEnumQ", "concrete interpreter endpoint"),
        ("Interp/FreeOmega", "FreeOmega", "canonical-model interpreter compositionality"),
        ("Interp", "generic", "structural interpretation or generic hitting infrastructure"),
    ):
        if path.startswith(prefix + "/"):
            return prefix, profile, disposition
    raise AssertionError("Module lacks an architectural owner: " + path)


def permitted(module, dependency):
    if module.startswith('API/') or dependency.startswith('API/'):
        return False
    if dependency in GATE_M and module not in GATE_M:
        return False
    def under(*prefixes):
        return any(dependency.startswith(p + "/") for p in prefixes)
    if external_validation(dependency) and not (
            external_validation(module) or module.startswith("Regression/")):
        return False
    if module.startswith("Prob/Domain/"):
        return under("Prob/Domain")
    if module.startswith("Prob/FreeOmega/Validation/"):
        return under("Prob/Domain", "Prob/Interface", "Prob/FreeOmega")
    if module in {"Prob/Backend/Common/DomainTransport", "Prob/Backend/Common/CountableCoupling", "Prob/Backend/Common/CountableRelationalLimit"}:
        return under("Prob/Domain", "Prob/Backend/Common")
    # A generic theorem layer may not silently fix its observable carrier.
    if ownership(module)[1] == "generic" and ownership(dependency)[1] == "FreeOmega":
        return False
    if module == "PTree":
        return under("Core")
    if module == "Eq":
        return dependency in {"Eq/PStruct", "Eq/PStrong", "Eq/PEutt", "Eq/Canonical"}
    if module == "PTreeFacts":
        return dependency in {"PTree", "Eq", "Eq/UnifiedFrontier", "Eq/PrimitiveStableHitting",
            "Eq/WellFormedness", "Eq/StableHittingComputation", "Eq/ProbabilisticTrace", "Eq/Bind", "Eq/Algebra", "Eq/Iter",
            "Eq/FreeOmega/Bind", "Eq/FreeOmega/Algebra", "Eq/FreeOmega/Iter",
            "Interp/Guarded", "Interp/FreeOmega/Atomic", "Interp/FreeOmega/MDP",
            "Interp/Unrestricted", "Interp/HandlerRelation", "Interp/HandlerFacts",
            "Interp/State", "Interp/Reader", "Interp/Writer", "Interp/Exception",
            "Interp/StateFacts", "Interp/StatePreservation", "Interp/StandardFacts",
            "Interp/ExceptionFacts", "Interp/FreeOmega/HandlerCompletion"}
    if module == "Semantics":
        return under("Semantics")
    if module.startswith("Core/"):
        return under("Core")
    if module == "Execution/Validation/SubEnumQ":
        return under("Core", "Execution", "Prob", "Eq")
    if module.startswith("Execution/Validation/"):
        return under("Core", "Execution", "Prob/Backend/Common", "Prob/Backend/EnumQ", "Prob/Backend/SubEnumQ")
    if module.startswith("Execution/Backend/"):
        return under("Core", "Execution", "Prob/Backend/Common", "Prob/Backend/EnumQ", "Prob/Backend/SubEnumQ")
    if module.startswith("Execution/"):
        return under("Core", "Execution") and not under("Execution/Backend")
    if module.startswith("Prob/Interface/"):
        return under("Prob/Interface")
    if module.startswith("Prob/FreeOmega/"):
        return under("Prob/Interface", "Prob/FreeOmega")
    if module.startswith("Prob/Backend/Common/"):
        return under("Prob/Interface", "Prob/Backend/Common")
    if module.startswith("Prob/Backend/MathComp/"):
        return under("Prob/Interface", "Prob/Backend/Common", "Prob/Backend/MathComp", "Prob/Domain")
    if module.startswith("Prob/Backend/SubEnumR/"):
        if module == "Prob/Backend/SubEnumR/RationalEmbedding":
            return under("Prob/Backend/SubEnumR", "Prob/Backend/SubEnumQ",
                         "Prob/Backend/EnumQ", "Prob/Backend/Common")
        return under("Prob/Interface", "Prob/FreeOmega", "Prob/Backend/Common",
                     "Prob/Backend/SubEnumR", "Prob/Domain")
    if module.startswith(("Prob/Backend/EnumQ/", "Prob/Backend/SubEnumQ/")):
        # SubEnumQ is a validated EnumQ carrier, not an unrelated implementation.
        # Realization/observation adapters legitimately cross this boundary.
        return under("Prob/Interface", "Prob/FreeOmega", "Prob/Backend/Common",
                     "Prob/Backend/EnumQ", "Prob/Backend/SubEnumQ", "Prob/Domain")
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
    roots = {m for m in edges if m.startswith("Interp/")}
    roots |= {m for m in {"Eq/PEutt", "Eq/Canonical", "PTree", "Eq", "PTreeFacts", "Semantics"} if m in edges}
    internal = {m for m in closure(edges, roots) if m.startswith("Eq/Internal/")}
    assert not internal, "Formal mainline depends on auxiliary internal machinery: " + str(sorted(internal))


def check_external_validation_boundary(edges):
    # Explicit validation adapters can live under Eq/Backend; they validate
    # reasoning and must not themselves be counted as reasoning roots.
    roots = {m for m in edges if not external_validation(m) and m.startswith(
        ("Core/", "Eq/", "Semantics/", "Interp/", "Execution/", "Examples/"))}
    roots |= {m for m in ("PTree", "Eq", "PTreeFacts", "Semantics") if m in edges}
    leaked = {m for m in closure(edges, roots) if external_validation(m)}
    assert not leaked, "Mainline depends on external validation: " + str(sorted(leaked))


def check_native_expectation_boundary(edges):
    # Native SubEnumQ validation precedes formal omega completion, even through
    # indirect finite-helper imports. Upper evaluators may use finite facts,
    # but finite facts must never depend on external validation in return.
    roots = {m for m in ("Prob/Backend/SubEnumQ/Expectation",
                         "Prob/Backend/SubEnumQ/Domain", "Prob/Backend/SubEnumR/Domain",
                         "Prob/Backend/SubEnumR/Representation", "Prob/Backend/SubEnumR/Measure") if m in edges}
    leaked = {m for m in closure(edges, roots) if "/FreeOmega/" in m}
    assert not leaked, "Native expectation/domain depends on FreeOmega: " + str(sorted(leaked))
    finite = "Prob/Backend/SubEnumQ/Expectation"
    if finite in edges:
        leaked = {m for m in closure(edges, {finite}) if external_validation(m)}
        assert not leaked, "Finite expectation depends on validation: " + str(sorted(leaked))


def aggregate_check(actual=None, expected=None):
    if expected is None:
        expected = sorted('PTree.' + p.relative_to(THEORIES).with_suffix('').as_posix().replace('/', '.')
                          for p in THEORIES.rglob('*.v')
                          if p != THEORIES / (AGGREGATE + '.v')
                          and p.relative_to(THEORIES).with_suffix('').as_posix() not in GATE_M)
    if actual is None:
        actual = re.findall(r'^Require (PTree\.[\w.]+)\.$',
                            (THEORIES / (AGGREGATE + '.v')).read_text(), re.M)
    assert actual == sorted(set(expected)), 'AllImports must contain every other Gate S module exactly once, sorted'


def check_mathcomp_native_sources(sources):
    """Reject the removed concrete completion, including simple local aliases.

    This is a source guard, not a Coq elaborator. The import-closure check
    independently excludes completion dependencies from all native modules.
    Generic arbitrary-MN completion theorems remain unrestricted.
    """
    for module, text in sources.items():
        code = re.sub(r'"(?:""|[^"\n])*"', '""', without_comments(text))
        assert not re.search(r'\bMathCompBehaviorMeasure\b', code), \
            'Removed behavioral alias: ' + module
        if module.startswith('Prob/Backend/MathComp/'):
            assert not re.search(r'\b(?:FreeOmega\w*|free_omega_\w*)\b', code), \
                'Native MathComp source mentions formal completion: ' + module
        native_names = {'MathCompKernelMeasure'}
        aliases = re.findall(
            r'\b(?:Notation|Let|Definition)\s+(\w+)[^\n]*?:=\s*\(?\s*@?\s*'
            r'((?:\w+\.)*\w+)\b', code)
        while True:
            extended = native_names | {name for name, target in aliases
                                       if target.rsplit('.', 1)[-1] in native_names}
            if extended == native_names:
                break
            native_names = extended
        names = '|'.join(re.escape(n) for n in sorted(native_names))
        assert not re.search(r'\b(?:FreeOmega|FreeOmegaAt)\s*\(?\s*@?\s*'
                             r'(?:\w+\.)*(?:' + names + r')\b', code), \
            'Removed MathComp completion instantiation: ' + module


def check_mathcomp_native_boundary(edges):
    roots = {m for m in edges if m.startswith('Prob/Backend/MathComp/')}
    leaked = {m for m in closure(edges, roots) if m.startswith('Prob/FreeOmega/')}
    assert not leaked, 'Native MathComp transitively loads completion: ' + str(sorted(leaked))


def graph():
    aggregate_check()
    check_mathcomp_native_sources({p.relative_to(THEORIES).with_suffix('').as_posix(): p.read_text()
                                  for p in THEORIES.rglob('*.v')})
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
    assert edges[AGGREGATE] == paths - {AGGREGATE} - GATE_M, "Incomplete safe AllImports"
    check_gate_boundary(edges)
    assert all(AGGREGATE not in ds for ds in edges.values()), "Aggregate used as library"
    for module, deps in edges.items():
        ownership(module)
        for dep in deps:
            assert permitted(module, dep), "Forbidden ownership edge: " + module + " -> " + dep
    check_auxiliary_boundary(edges)
    check_external_validation_boundary(edges)
    check_native_expectation_boundary(edges)
    check_mathcomp_native_boundary(edges)
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
        f"- Safe AllImports covers {len(ordinary - GATE_M)} other Gate S modules; {len(GATE_M)} exact-allowlisted Gate M modules are excluded.",
        "- No Gate S module (including regressions/aggregates) imports Gate M, directly or transitively.",
        "- Every edge is checked against the ownership policy, not merely displayed as debt.",
        "- Core has no local probability dependency; Prob has no tree-theory dependency.",
        "- Generic interfaces and FreeOmega measure infrastructure import no concrete backend.",
        "- Concrete probability modules name Common/EnumQ/SubEnumQ/SubEnumR/MathComp ownership; Common cannot import a native carrier.",
        "- Native SubEnumQ expectation/domain closures exclude FreeOmega; finite expectation also excludes external validation.",
        "- MathComp and EnumQ/SubEnumQ do not depend on each other; EnumQ/SubEnumQ realization adapters may reuse each other.",
        "- MathComp native sources and their transitive dependencies exclude formal completion; no MathComp behavioral alias or concrete FreeOmega instantiation is maintained.",
        "- Eq imports no Interp/Semantics; Semantics imports no Interp. Canonical routing is owned by Eq; there is no API namespace or Gate M reverse-dependency exception.",
        "- PTree exports only Core; Eq exports relation owners/notations; PTreeFacts aggregates selected reasoning modules without concrete backends.",
        "- Generic/canonical-model Eq, Semantics and Interp modules import no concrete backend endpoint.",
        "- No maintained library imports Regression, Examples or Experimental.",
        "- Cases do not depend on tests. Experimental has no remaining source module.", "",
        "- The peutt/Interp/public-facade dependency closure contains no Eq/Internal module.", "",
        "- Prob/Domain depends only on mathematical libraries and itself, never the existing probability interfaces or FreeOmega.",
        "- The Core/Eq/Semantics/Interp/Examples and public entry-point closures exclude external validation; explicit validation adapters are not reasoning roots.", "",
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
             "SubEnumQ domain soundness does not use this branch. Regression-only leaves "
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
